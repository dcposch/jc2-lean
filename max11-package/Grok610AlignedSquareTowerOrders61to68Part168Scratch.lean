import Grok610AlignedSquareSourceWrapperScratch
import Grok610PoleCeilingLemmaScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section AlignedSquareTowerHeads610

variable {k : Type*} [Field k] [CharZero k]

def alignedSquareMuZeroQ8QuotOne610c0 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (7113144729600 : R) * h ^ 19 * w1 * e1n ^ 7
    - (1070551227432960 : R) * h ^ 19 * w1 * e1n ^ 4 * a0
    - (12638572385402880 : R) * h ^ 19 * w1 * e1n * a0 ^ 2
    + (1185524121600 : R) * h ^ 19 * e1n ^ 6 * e3
    - (111515752857600 : R) * h ^ 19 * e1n ^ 5 * a1
    + (178425204572160 : R) * h ^ 19 * e1n ^ 3 * e3 * a0
    + (70214291030016 : R) * h ^ 19 * e1n ^ 3 * b1
    - (13691786750853120 : R) * h ^ 19 * e1n ^ 2 * a1 * a0
    + (2106428730900480 : R) * h ^ 19 * e3 * a0 ^ 2
    + (58498535041007616 : R) * h ^ 19 * a0 * b1

def alignedSquareMuZeroQ8QuotOne610c1 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (39122296012800 : R) * h ^ 17 * w1 ^ 3 * e1n ^ 6
    - (1873464648007680 : R) * h ^ 17 * w1 ^ 3 * e1n ^ 3 * a0
    - (37915717156208640 : R) * h ^ 17 * w1 ^ 3 * a0 ^ 2
    - (26674292736000 : R) * h ^ 17 * w1 ^ 2 * e1n ^ 5 * e3
    + (1254552219648000 : R) * h ^ 17 * w1 ^ 2 * e1n ^ 4 * a1
    - (401456710287360 : R) * h ^ 17 * w1 ^ 2 * e1n ^ 2 * e3 * a0
    - (473946464452608 : R) * h ^ 17 * w1 ^ 2 * e1n ^ 2 * b1
    - (20537680126279680 : R) * h ^ 17 * w1 ^ 2 * e1n * a1 * a0
    + (408891093811200 : R) * h ^ 17 * w1 * e1n ^ 5 * a2
    + (4206698496000 : R) * h ^ 17 * w1 * e1n ^ 4 * e3 ^ 2

def alignedSquareMuZeroQ8QuotOne610c2 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (475800545525760 : R) * h ^ 17 * w1 * e1n ^ 3 * e3 * a1
    - (304261927796736 : R) * h ^ 17 * w1 * e1n ^ 3 * b2
    + (22819644584755200 : R) * h ^ 17 * w1 * e1n ^ 2 * a2 * a0
    + (11409822292377600 : R) * h ^ 17 * w1 * e1n ^ 2 * a1 ^ 2
    + (93908002406400 : R) * h ^ 17 * w1 * e1n * e3 ^ 2 * a0
    + (140428582060032 : R) * h ^ 17 * w1 * e1n * e3 * b1
    - (2808571641200640 : R) * h ^ 17 * w1 * e3 * a1 * a0
    - (9749755840167936 : R) * h ^ 17 * w1 * a1 * b1
    - (19499511680335872 : R) * h ^ 17 * w1 * a0 * b2
    - (61953196032000 : R) * h ^ 17 * e1n ^ 4 * e3 * a2

def alignedSquareMuZeroQ8QuotOne610c3 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (38032740974592 : R) * h ^ 17 * e1n ^ 4 * b3
    - (169967616000 : R) * h ^ 17 * e1n ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * h ^ 17 * e1n ^ 3 * a2 * a1
    + (29737534095360 : R) * h ^ 17 * e1n ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * h ^ 17 * e1n ^ 2 * e3 * b2
    - (3042619277967360 : R) * h ^ 17 * e1n * e3 * a2 * a0
    - (1521309638983680 : R) * h ^ 17 * e1n * e3 * a1 ^ 2
    - (3249918613389312 : R) * h ^ 17 * e1n * a2 * b1
    - (6499837226778624 : R) * h ^ 17 * e1n * a1 * b2
    - (9749755840167936 : R) * h ^ 17 * e1n * a0 * b3

def alignedSquareMuZeroQ8QuotOne610c4 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (2086844497920 : R) * h ^ 17 * e3 ^ 3 * a0
    - (6687075336192 : R) * h ^ 17 * e3 ^ 2 * b1
    + (113747151468625920 : R) * h ^ 17 * a2 * a1 * a0
    + (18957858578104320 : R) * h ^ 17 * a1 ^ 3
    + (208859712122880 : R) * h ^ 15 * w1 ^ 5 * e1n ^ 5
    + (10237146112327680 : R) * h ^ 15 * w1 ^ 5 * e1n ^ 2 * a0
    - (46787569920000 : R) * h ^ 15 * w1 ^ 4 * e1n ^ 4 * e3
    + (4937359957770240 : R) * h ^ 15 * w1 ^ 4 * e1n ^ 3 * a1
    - (2544319940198400 : R) * h ^ 15 * w1 ^ 4 * e1n * e3 * a0
    + (65825897840640 : R) * h ^ 15 * w1 ^ 4 * e1n * b1

def alignedSquareMuZeroQ8QuotOne610c5 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (49961856461045760 : R) * h ^ 15 * w1 ^ 4 * a1 * a0
    - (418184073216000 : R) * h ^ 15 * w1 ^ 3 * e1n ^ 4 * a2
    - (3441844224000 : R) * h ^ 15 * w1 ^ 3 * e1n ^ 3 * e3 ^ 2
    - (624488216002560 : R) * h ^ 15 * w1 ^ 3 * e1n ^ 2 * e3 * a1
    + (579267900997632 : R) * h ^ 15 * w1 ^ 3 * e1n ^ 2 * b2
    + (57049111461888000 : R) * h ^ 15 * w1 ^ 3 * e1n * a2 * a0
    + (28524555730944000 : R) * h ^ 15 * w1 ^ 3 * e1n * a1 ^ 2
    + (117385003008000 : R) * h ^ 15 * w1 ^ 3 * e3 ^ 2 * a0
    - (25076532510720 : R) * h ^ 15 * w1 ^ 3 * e3 * b1
    + (557578764288000 : R) * h ^ 15 * w1 ^ 2 * e1n ^ 3 * e3 * a2

def alignedSquareMuZeroQ8QuotOne610c6 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (570491114618880 : R) * h ^ 15 * w1 ^ 2 * e1n ^ 3 * b3
    + (1147281408000 : R) * h ^ 15 * w1 ^ 2 * e1n ^ 2 * e3 ^ 3
    - (10839331177758720 : R) * h ^ 15 * w1 ^ 2 * e1n ^ 2 * a2 * a1
    - (44606301143040 : R) * h ^ 15 * w1 ^ 2 * e1n * e3 ^ 2 * a1
    - (210642873090048 : R) * h ^ 15 * w1 ^ 2 * e1n * e3 * b2
    - (2281964458475520 : R) * h ^ 15 * w1 ^ 2 * e3 * a2 * a0
    - (1140982229237760 : R) * h ^ 15 * w1 ^ 2 * e3 * a1 ^ 2
    + (2437438960041984 : R) * h ^ 15 * w1 ^ 2 * a2 * b1
    + (4874877920083968 : R) * h ^ 15 * w1 ^ 2 * a1 * b2
    + (7312316880125952 : R) * h ^ 15 * w1 ^ 2 * a0 * b3

def alignedSquareMuZeroQ8QuotOne610c7 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (160582684114944 : R) * h ^ 15 * w1 * e1n ^ 4 * b4
    - (6423307364597760 : R) * h ^ 15 * w1 * e1n ^ 3 * a2 ^ 2
    - (79300090920960 : R) * h ^ 15 * w1 * e1n ^ 2 * e3 ^ 2 * a2
    - (152130963898368 : R) * h ^ 15 * w1 * e1n ^ 2 * e3 * b3
    - (54389637120 : R) * h ^ 15 * w1 * e1n * e3 ^ 4
    + (5071032129945600 : R) * h ^ 15 * w1 * e1n * e3 * a2 * a1
    + (7583143431241728 : R) * h ^ 15 * w1 * e1n * a2 * b2
    + (11374715146862592 : R) * h ^ 15 * w1 * e1n * a1 * b3
    + (15166286862483456 : R) * h ^ 15 * w1 * e1n * a0 * b4
    + (3478074163200 : R) * h ^ 15 * w1 * e3 ^ 3 * a1

def alignedSquareMuZeroQ8QuotOne610c8 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (15603175784448 : R) * h ^ 15 * w1 * e3 ^ 2 * b2
    - (37915717156208640 : R) * h ^ 15 * w1 * a2 ^ 2 * a0
    - (37915717156208640 : R) * h ^ 15 * w1 * a2 * a1 ^ 2
    + (13381890342912 : R) * h ^ 15 * e1n ^ 5 * b5
    - (22537920577536 : R) * h ^ 15 * e1n ^ 3 * e3 * b4
    + (802913420574720 : R) * h ^ 15 * e1n ^ 2 * e3 * a2 ^ 2
    + (1895785857810432 : R) * h ^ 15 * e1n ^ 2 * a2 * b3
    + (2527714477080576 : R) * h ^ 15 * e1n ^ 2 * a1 * b4
    + (3159643096350720 : R) * h ^ 15 * e1n ^ 2 * a0 * b5
    + (2202780303360 : R) * h ^ 15 * e1n * e3 ^ 3 * a2

def alignedSquareMuZeroQ8QuotOne610c9 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (7801587892224 : R) * h ^ 15 * e1n * e3 ^ 2 * b3
    - (41075360252559360 : R) * h ^ 15 * e1n * a2 ^ 2 * a1
    + (453246976 : R) * h ^ 15 * e3 ^ 5
    - (169034404331520 : R) * h ^ 15 * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * h ^ 15 * e3 * a2 * b2
    - (1083306204463104 : R) * h ^ 15 * e3 * a1 * b3
    - (1444408272617472 : R) * h ^ 15 * e3 * a0 * b4
    - (516534771916800 : R) * h ^ 13 * w1 ^ 7 * e1n ^ 4
    - (2328373457879040 : R) * h ^ 13 * w1 ^ 7 * e1n * a0
    + (259751681280000 : R) * h ^ 13 * w1 ^ 6 * e1n ^ 3 * e3

def alignedSquareMuZeroQ8QuotOne610c10 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (7713405230469120 : R) * h ^ 13 * w1 ^ 6 * e1n ^ 2 * a1
    + (537476582522880 : R) * h ^ 13 * w1 ^ 6 * e3 * a0
    - (470184984576 : R) * h ^ 13 * w1 ^ 6 * b1
    - (6732763578777600 : R) * h ^ 13 * w1 ^ 5 * e1n ^ 3 * a2
    - (41560269004800 : R) * h ^ 13 * w1 ^ 5 * e1n ^ 2 * e3 ^ 2
    + (2274921358295040 : R) * h ^ 13 * w1 ^ 5 * e1n * e3 * a1
    - (39495538704384 : R) * h ^ 13 * w1 ^ 5 * e1n * b2
    - (28239310173634560 : R) * h ^ 13 * w1 ^ 5 * a2 * a0
    - (14119655086817280 : R) * h ^ 13 * w1 ^ 5 * a1 ^ 2
    + (1645786652590080 : R) * h ^ 13 * w1 ^ 4 * e1n ^ 2 * e3 * a2

def alignedSquareMuZeroQ8QuotOne610c11 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (470655169560576 : R) * h ^ 13 * w1 ^ 4 * e1n ^ 2 * b3
    + (2257594859520 : R) * h ^ 13 * w1 ^ 4 * e1n * e3 ^ 3
    - (68696638385356800 : R) * h ^ 13 * w1 ^ 4 * e1n * a2 * a1
    - (141351107788800 : R) * h ^ 13 * w1 ^ 4 * e3 ^ 2 * a1
    + (14627977297920 : R) * h ^ 13 * w1 ^ 4 * e3 * b2
    - (718396218408960 : R) * h ^ 13 * w1 ^ 3 * e1n ^ 3 * b4
    - (8430590916034560 : R) * h ^ 13 * w1 ^ 3 * e1n ^ 2 * a2 ^ 2
    - (69387579555840 : R) * h ^ 13 * w1 ^ 3 * e1n * e3 ^ 2 * a2
    + (193089300332544 : R) * h ^ 13 * w1 ^ 3 * e1n * e3 * b3
    - (23795466240 : R) * h ^ 13 * w1 ^ 3 * e3 ^ 4

def alignedSquareMuZeroQ8QuotOne610c12 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (6338790162432000 : R) * h ^ 13 * w1 ^ 3 * e3 * a2 * a1
    - (1354132755578880 : R) * h ^ 13 * w1 ^ 3 * a2 * b2
    - (2031199133368320 : R) * h ^ 13 * w1 ^ 3 * a1 * b3
    - (2708265511157760 : R) * h ^ 13 * w1 ^ 3 * a0 * b4
    - (351274621501440 : R) * h ^ 13 * w1 ^ 2 * e1n ^ 4 * b5
    + (253551606497280 : R) * h ^ 13 * w1 ^ 2 * e1n ^ 2 * e3 * b4
    - (1204370130862080 : R) * h ^ 13 * w1 ^ 2 * e1n * e3 * a2 ^ 2
    - (8531036360146944 : R) * h ^ 13 * w1 ^ 2 * e1n * a2 * b3
    - (11374715146862592 : R) * h ^ 13 * w1 ^ 2 * e1n * a1 * b4
    - (14218393933578240 : R) * h ^ 13 * w1 ^ 2 * e1n * a0 * b5

def alignedSquareMuZeroQ8QuotOne610c13 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (1652085227520 : R) * h ^ 13 * w1 ^ 2 * e3 ^ 3 * a2
    - (17553572757504 : R) * h ^ 13 * w1 ^ 2 * e3 ^ 2 * b3
    - (30806520189419520 : R) * h ^ 13 * w1 ^ 2 * a2 ^ 2 * a1
    - (66909451714560 : R) * h ^ 13 * w1 * e1n ^ 5 * b6
    + (89212602286080 : R) * h ^ 13 * w1 * e1n ^ 3 * e3 * b5
    - (5476714700341248 : R) * h ^ 13 * w1 * e1n ^ 2 * a2 * b4
    - (6845893375426560 : R) * h ^ 13 * w1 * e1n ^ 2 * a1 * b5
    - (8215072050511872 : R) * h ^ 13 * w1 * e1n ^ 2 * a0 * b6
    - (22537920577536 : R) * h ^ 13 * w1 * e1n * e3 ^ 2 * b4
    + (22819644584755200 : R) * h ^ 13 * w1 * e1n * a2 ^ 3

def alignedSquareMuZeroQ8QuotOne610c14 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (140862003609600 : R) * h ^ 13 * w1 * e3 ^ 2 * a2 ^ 2
    + (1263857238540288 : R) * h ^ 13 * w1 * e3 * a2 * b3
    + (1685142984720384 : R) * h ^ 13 * w1 * e3 * a1 * b4
    + (2106428730900480 : R) * h ^ 13 * w1 * e3 * a0 * b5
    - (4336723722240 : R) * h ^ 13 * e1n ^ 6 * b7
    + (8921260228608 : R) * h ^ 13 * e1n ^ 4 * e3 * b6
    - (760654819491840 : R) * h ^ 13 * e1n ^ 3 * a2 * b5
    - (912785783390208 : R) * h ^ 13 * e1n ^ 3 * a1 * b6
    - (1064916747288576 : R) * h ^ 13 * e1n ^ 3 * a0 * b7
    - (4695400120320 : R) * h ^ 13 * e1n ^ 2 * e3 ^ 2 * b5

def alignedSquareMuZeroQ8QuotOne610c15 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (561714328240128 : R) * h ^ 13 * e1n * e3 * a2 * b4
    + (702142910300160 : R) * h ^ 13 * e1n * e3 * a1 * b5
    + (842571492360192 : R) * h ^ 13 * e1n * e3 * a0 * b6
    + (385263599616 : R) * h ^ 13 * e3 ^ 3 * b4
    - (1521309638983680 : R) * h ^ 13 * e3 * a2 ^ 3
    - (14624633760251904 : R) * h ^ 13 * a2 ^ 2 * b3
    - (38999023360671744 : R) * h ^ 13 * a2 * a1 * b4
    - (48748779200839680 : R) * h ^ 13 * a2 * a0 * b5
    - (24374389600419840 : R) * h ^ 13 * a1 ^ 2 * b5
    - (58498535041007616 : R) * h ^ 13 * a1 * a0 * b6

def alignedSquareMuZeroQ8QuotOne610c16 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (34124145440587776 : R) * h ^ 13 * a0 ^ 2 * b7
    + (25607321026560 : R) * h ^ 12 * w1 * e1n ^ 6 * b8n
    + (3853984418758656 : R) * h ^ 12 * w1 * e1n ^ 3 * a0 * b8n
    + (45498860587450368 : R) * h ^ 12 * w1 * a0 ^ 2 * b8n
    - (3304170455040 : R) * h ^ 12 * e1n ^ 5 * e3 * b8n
    + (321165368229888 : R) * h ^ 12 * e1n ^ 4 * a1 * b8n
    - (405682570395648 : R) * h ^ 12 * e1n ^ 2 * e3 * a0 * b8n
    + (30332573724966912 : R) * h ^ 12 * e1n * a1 * a0 * b8n
    + (205018291296000 : R) * h ^ 11 * w1 ^ 9 * e1n ^ 3
    + (20751991603200 : R) * h ^ 11 * w1 ^ 9 * a0

def alignedSquareMuZeroQ8QuotOne610c17 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (118279783440000 : R) * h ^ 11 * w1 ^ 8 * e1n ^ 2 * e3
    + (1068273617748480 : R) * h ^ 11 * w1 ^ 8 * e1n * a1
    + (5177815799869440 : R) * h ^ 11 * w1 ^ 7 * e1n ^ 2 * a2
    + (21307883950080 : R) * h ^ 11 * w1 ^ 7 * e1n * e3 ^ 2
    - (258708161986560 : R) * h ^ 11 * w1 ^ 7 * e3 * a1
    + (156728328192 : R) * h ^ 11 * w1 ^ 7 * b2
    - (1714090051215360 : R) * h ^ 11 * w1 ^ 6 * e1n * e3 * a2
    + (18102121906176 : R) * h ^ 11 * w1 ^ 6 * e1n * b3
    - (1175644753920 : R) * h ^ 11 * w1 ^ 6 * e3 ^ 3
    + (14511867728117760 : R) * h ^ 11 * w1 ^ 6 * a2 * a1

def alignedSquareMuZeroQ8QuotOne610c18 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (313770113040384 : R) * h ^ 11 * w1 ^ 5 * e1n ^ 2 * b4
    + (30711438336983040 : R) * h ^ 11 * w1 ^ 5 * e1n * a2 ^ 2
    + (126384519905280 : R) * h ^ 11 * w1 ^ 5 * e3 ^ 2 * a2
    - (6582589784064 : R) * h ^ 11 * w1 ^ 5 * e3 * b3
    + (710912924467200 : R) * h ^ 11 * w1 ^ 4 * e1n ^ 3 * b5
    - (139453383573504 : R) * h ^ 11 * w1 ^ 4 * e1n * e3 * b4
    - (3816479910297600 : R) * h ^ 11 * w1 ^ 4 * e3 * a2 ^ 2
    + (592433080565760 : R) * h ^ 11 * w1 ^ 4 * a2 * b3
    + (789910774087680 : R) * h ^ 11 * w1 ^ 4 * a1 * b4
    + (987388467609600 : R) * h ^ 11 * w1 ^ 4 * a0 * b5

def alignedSquareMuZeroQ8QuotOne610c19 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (538621086302208 : R) * h ^ 11 * w1 ^ 3 * e1n ^ 4 * b6
    - (299331757670400 : R) * h ^ 11 * w1 ^ 3 * e1n ^ 2 * e3 * b5
    + (6951214811971584 : R) * h ^ 11 * w1 ^ 3 * e1n * a2 * b4
    + (8689018514964480 : R) * h ^ 11 * w1 ^ 3 * e1n * a1 * b5
    + (10426822217957376 : R) * h ^ 11 * w1 ^ 3 * e1n * a0 * b6
    + (14302911135744 : R) * h ^ 11 * w1 ^ 3 * e3 ^ 2 * b4
    + (28524555730944000 : R) * h ^ 11 * w1 ^ 3 * a2 ^ 3
    + (175637310750720 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 5 * b7
    - (187346464800768 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 3 * e3 * b6
    + (8557366719283200 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 2 * a2 * b5

def alignedSquareMuZeroQ8QuotOne610c20 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (10268840063139840 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 2 * a1 * b6
    + (11980313406996480 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 2 * a0 * b7
    + (35215500902400 : R) * h ^ 11 * w1 ^ 2 * e1n * e3 ^ 2 * b5
    - (1263857238540288 : R) * h ^ 11 * w1 ^ 2 * e3 * a2 * b4
    - (1579821548175360 : R) * h ^ 11 * w1 ^ 2 * e3 * a1 * b5
    - (1895785857810432 : R) * h ^ 11 * w1 ^ 2 * e3 * a0 * b6
    - (43367237222400 : R) * h ^ 11 * w1 * e1n ^ 4 * e3 * b7
    + (2890488314068992 : R) * h ^ 11 * w1 * e1n ^ 3 * a2 * b6
    + (3372236366413824 : R) * h ^ 11 * w1 * e1n ^ 3 * a1 * b7
    + (17842520457216 : R) * h ^ 11 * w1 * e1n ^ 2 * e3 ^ 2 * b6

def alignedSquareMuZeroQ8QuotOne610c21 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (1521309638983680 : R) * h ^ 11 * w1 * e1n * e3 * a2 * b5
    - (1825571566780416 : R) * h ^ 11 * w1 * e1n * e3 * a1 * b6
    - (2129833494577152 : R) * h ^ 11 * w1 * e1n * e3 * a0 * b7
    - (1043422248960 : R) * h ^ 11 * w1 * e3 ^ 3 * b5
    + (22749430293725184 : R) * h ^ 11 * w1 * a2 ^ 2 * b4
    + (56873575734312960 : R) * h ^ 11 * w1 * a2 * a1 * b5
    + (68248290881175552 : R) * h ^ 11 * w1 * a2 * a0 * b6
    + (34124145440587776 : R) * h ^ 11 * w1 * a1 ^ 2 * b6
    + (79623006028038144 : R) * h ^ 11 * w1 * a1 * a0 * b7
    + (281019697201152 : R) * h ^ 11 * e1n ^ 4 * a2 * b7

def alignedSquareMuZeroQ8QuotOne610c22 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (2312919318528 : R) * h ^ 11 * e1n ^ 3 * e3 ^ 2 * b7
    - (304261927796736 : R) * h ^ 11 * e1n ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * h ^ 11 * e1n ^ 2 * e3 * a1 * b7
    - (417368899584 : R) * h ^ 11 * e1n * e3 ^ 3 * b6
    + (9478929289052160 : R) * h ^ 11 * e1n * a2 ^ 2 * b5
    + (22749430293725184 : R) * h ^ 11 * e1n * a2 * a1 * b6
    + (26541002009346048 : R) * h ^ 11 * e1n * a2 * a0 * b7
    + (13270501004673024 : R) * h ^ 11 * e1n * a1 ^ 2 * b7
    + (39007939461120 : R) * h ^ 11 * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * h ^ 11 * e3 ^ 2 * a1 * b6

def alignedSquareMuZeroQ8QuotOne610c23 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (54611115245568 : R) * h ^ 11 * e3 ^ 2 * a0 * b7
    - (323395683287040 : R) * h ^ 10 * w1 ^ 3 * e1n ^ 5 * b8n
    - (12931131931361280 : R) * h ^ 10 * w1 ^ 3 * e1n ^ 2 * a0 * b8n
    + (111515752857600 : R) * h ^ 10 * w1 ^ 2 * e1n ^ 4 * e3 * b8n
    - (6744472732827648 : R) * h ^ 10 * w1 ^ 2 * e1n ^ 3 * a1 * b8n
    + (3042619277967360 : R) * h ^ 10 * w1 ^ 2 * e1n * e3 * a0 * b8n
    - (68248290881175552 : R) * h ^ 10 * w1 ^ 2 * a1 * a0 * b8n
    - (1338189034291200 : R) * h ^ 10 * w1 * e1n ^ 4 * a2 * b8n
    - (11013901516800 : R) * h ^ 10 * w1 * e1n ^ 3 * e3 ^ 2 * b8n
    + (1284661472919552 : R) * h ^ 10 * w1 * e1n ^ 2 * e3 * a1 * b8n

def alignedSquareMuZeroQ8QuotOne610c24 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (65720576404094976 : R) * h ^ 10 * w1 * e1n * a2 * a0 * b8n
    - (32860288202047488 : R) * h ^ 10 * w1 * e1n * a1 ^ 2 * b8n
    - (135227523465216 : R) * h ^ 10 * w1 * e3 ^ 2 * a0 * b8n
    + (142740163657728 : R) * h ^ 10 * e1n ^ 3 * e3 * a2 * b8n
    + (293704040448 : R) * h ^ 10 * e1n ^ 2 * e3 ^ 3 * b8n
    - (10953429400682496 : R) * h ^ 10 * e1n ^ 2 * a2 * a1 * b8n
    - (45075841155072 : R) * h ^ 10 * e1n * e3 ^ 2 * a1 * b8n
    + (3370285969440768 : R) * h ^ 10 * e3 * a2 * a0 * b8n
    + (1685142984720384 : R) * h ^ 10 * e3 * a1 ^ 2 * b8n
    - (14193574012800 : R) * h ^ 9 * w1 ^ 11 * e1n ^ 2

def alignedSquareMuZeroQ8QuotOne610c25 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (7517337347520 : R) * h ^ 9 * w1 ^ 10 * e1n * e3
    - (6522826527360 : R) * h ^ 9 * w1 ^ 10 * a1
    - (472460881052160 : R) * h ^ 9 * w1 ^ 9 * e1n * a2
    - (972141730560 : R) * h ^ 9 * w1 ^ 9 * e3 ^ 2
    + (118697068638720 : R) * h ^ 9 * w1 ^ 8 * e3 * a2
    - (44079842304 : R) * h ^ 9 * w1 ^ 8 * b3
    - (7470716977152 : R) * h ^ 9 * w1 ^ 7 * e1n * b4
    - (3492560186818560 : R) * h ^ 9 * w1 ^ 7 * a2 ^ 2
    - (185211525058560 : R) * h ^ 9 * w1 ^ 6 * e1n ^ 2 * b5
    + (2681795837952 : R) * h ^ 9 * w1 ^ 6 * e3 * b4

def alignedSquareMuZeroQ8QuotOne610c26 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (597166856552448 : R) * h ^ 9 * w1 ^ 5 * e1n ^ 3 * b6
    + (87158364733440 : R) * h ^ 9 * w1 ^ 5 * e1n * e3 * b5
    - (236973232226304 : R) * h ^ 9 * w1 ^ 5 * a2 * b4
    - (296216540282880 : R) * h ^ 9 * w1 ^ 5 * a1 * b5
    - (355459848339456 : R) * h ^ 9 * w1 ^ 5 * a0 * b6
    - (654574236825600 : R) * h ^ 9 * w1 ^ 4 * e1n ^ 4 * b7
    + (284365169786880 : R) * h ^ 9 * w1 ^ 4 * e1n ^ 2 * e3 * b6
    - (4706551695605760 : R) * h ^ 9 * w1 ^ 4 * e1n * a2 * b5
    - (5647862034726912 : R) * h ^ 9 * w1 ^ 4 * e1n * a1 * b6
    - (6589172373848064 : R) * h ^ 9 * w1 ^ 4 * e1n * a0 * b7

def alignedSquareMuZeroQ8QuotOne610c27 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (9684262748160 : R) * h ^ 9 * w1 ^ 4 * e3 ^ 2 * b5
    + (279285007712256 : R) * h ^ 9 * w1 ^ 3 * e1n ^ 3 * e3 * b7
    - (9698348948520960 : R) * h ^ 9 * w1 ^ 3 * e1n ^ 2 * a2 * b6
    - (11314740439941120 : R) * h ^ 9 * w1 ^ 3 * e1n ^ 2 * a1 * b7
    - (39910901022720 : R) * h ^ 9 * w1 ^ 3 * e1n * e3 ^ 2 * b6
    + (965446501662720 : R) * h ^ 9 * w1 ^ 3 * e3 * a2 * b5
    + (1158535801995264 : R) * h ^ 9 * w1 ^ 3 * e3 * a1 * b6
    + (1351625102327808 : R) * h ^ 9 * w1 ^ 3 * e3 * a0 * b7
    - (5901413641224192 : R) * h ^ 9 * w1 ^ 2 * e1n ^ 3 * a2 * b7
    - (36428479266816 : R) * h ^ 9 * w1 ^ 2 * e1n ^ 2 * e3 ^ 2 * b7

def alignedSquareMuZeroQ8QuotOne610c28 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (2281964458475520 : R) * h ^ 9 * w1 ^ 2 * e1n * e3 * a2 * b6
    + (2662291868221440 : R) * h ^ 9 * w1 ^ 2 * e1n * e3 * a1 * b7
    + (1565133373440 : R) * h ^ 9 * w1 ^ 2 * e3 ^ 3 * b6
    - (21327590900367360 : R) * h ^ 9 * w1 ^ 2 * a2 ^ 2 * b5
    - (51186218160881664 : R) * h ^ 9 * w1 ^ 2 * a2 * a1 * b6
    - (59717254521028608 : R) * h ^ 9 * w1 ^ 2 * a2 * a0 * b7
    - (29858627260514304 : R) * h ^ 9 * w1 ^ 2 * a1 ^ 2 * b7
    + (1124078788804608 : R) * h ^ 9 * w1 * e1n ^ 2 * e3 * a2 * b7
    + (1541946212352 : R) * h ^ 9 * w1 * e1n * e3 ^ 3 * b7
    - (24645216151535616 : R) * h ^ 9 * w1 * e1n * a2 ^ 2 * b6

def alignedSquareMuZeroQ8QuotOne610c29 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (57505504353583104 : R) * h ^ 9 * w1 * e1n * a2 * a1 * b7
    - (101420642598912 : R) * h ^ 9 * w1 * e3 ^ 2 * a2 * b6
    - (118324083032064 : R) * h ^ 9 * w1 * e3 ^ 2 * a1 * b7
    - (4792125362798592 : R) * h ^ 9 * e1n ^ 2 * a2 ^ 2 * b7
    - (39441361010688 : R) * h ^ 9 * e1n * e3 ^ 2 * a2 * b7
    - (13525843968 : R) * h ^ 9 * e3 ^ 4 * b7
    + (1263857238540288 : R) * h ^ 9 * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * h ^ 9 * e3 * a2 * a1 * b7
    + (673276357877760 : R) * h ^ 8 * w1 ^ 5 * e1n ^ 4 * b8n
    + (3765241356484608 : R) * h ^ 8 * w1 ^ 5 * e1n * a0 * b8n

def alignedSquareMuZeroQ8QuotOne610c30 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (332482152038400 : R) * h ^ 8 * w1 ^ 4 * e1n ^ 3 * e3 * b8n
    + (10237146112327680 : R) * h ^ 8 * w1 ^ 4 * e1n ^ 2 * a1 * b8n
    - (836720301441024 : R) * h ^ 8 * w1 ^ 4 * e3 * a0 * b8n
    + (8617937380835328 : R) * h ^ 8 * w1 ^ 3 * e1n ^ 3 * a2 * b8n
    + (53197144326144 : R) * h ^ 8 * w1 ^ 3 * e1n ^ 2 * e3 ^ 2 * b8n
    - (2873584873635840 : R) * h ^ 8 * w1 ^ 3 * e1n * e3 * a1 * b8n
    + (41707288871829504 : R) * h ^ 8 * w1 ^ 3 * a2 * a0 * b8n
    + (20853644435914752 : R) * h ^ 8 * w1 ^ 3 * a1 ^ 2 * b8n
    - (2248157577609216 : R) * h ^ 8 * w1 ^ 2 * e1n ^ 2 * e3 * a2 * b8n
    - (3083892424704 : R) * h ^ 8 * w1 ^ 2 * e1n * e3 ^ 3 * b8n

def alignedSquareMuZeroQ8QuotOne610c31 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (82150720505118720 : R) * h ^ 8 * w1 ^ 2 * e1n * a2 * a1 * b8n
    + (169034404331520 : R) * h ^ 8 * w1 ^ 2 * e3 ^ 2 * a1 * b8n
    + (17342929884413952 : R) * h ^ 8 * w1 * e1n ^ 2 * a2 ^ 2 * b8n
    + (142740163657728 : R) * h ^ 8 * w1 * e1n * e3 ^ 2 * a2 * b8n
    + (48950673408 : R) * h ^ 8 * w1 * e3 ^ 4 * b8n
    - (7302286267121664 : R) * h ^ 8 * w1 * e3 * a2 * a1 * b8n
    - (1217047711186944 : R) * h ^ 8 * e1n * e3 * a2 ^ 2 * b8n
    - (1669475598336 : R) * h ^ 8 * e3 ^ 3 * a2 * b8n
    + (45498860587450368 : R) * h ^ 8 * a2 ^ 2 * a1 * b8n
    + (69754744080 : R) * h ^ 7 * w1 ^ 13 * e1n

def alignedSquareMuZeroQ8QuotOne610c32 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (24284496600 : R) * h ^ 7 * w1 ^ 12 * e3
    + (2062916968320 : R) * h ^ 7 * w1 ^ 11 * a2
    + (11972302848 : R) * h ^ 7 * w1 ^ 9 * b4
    + (2918248819200 : R) * h ^ 7 * w1 ^ 8 * e1n * b5
    + (100543399317504 : R) * h ^ 7 * w1 ^ 7 * e1n ^ 2 * b6
    - (1037599580160 : R) * h ^ 7 * w1 ^ 7 * e3 * b5
    + (445110481041408 : R) * h ^ 7 * w1 ^ 6 * e1n ^ 3 * b7
    - (49389740015616 : R) * h ^ 7 * w1 ^ 6 * e1n * e3 * b6
    + (90510609530880 : R) * h ^ 7 * w1 ^ 6 * a2 * b5
    + (108612731437056 : R) * h ^ 7 * w1 ^ 6 * a1 * b6

def alignedSquareMuZeroQ8QuotOne610c33 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (126714853343232 : R) * h ^ 7 * w1 ^ 6 * a0 * b7
    - (232231555325952 : R) * h ^ 7 * w1 ^ 5 * e1n ^ 2 * e3 * b7
    + (2823931017363456 : R) * h ^ 7 * w1 ^ 5 * e1n * a2 * b6
    + (3294586186924032 : R) * h ^ 7 * w1 ^ 5 * e1n * a1 * b7
    + (5810557648896 : R) * h ^ 7 * w1 ^ 5 * e3 ^ 2 * b6
    + (8957502848286720 : R) * h ^ 7 * w1 ^ 4 * e1n ^ 2 * a2 * b7
    + (36862151639040 : R) * h ^ 7 * w1 ^ 4 * e1n * e3 ^ 2 * b7
    - (627540226080768 : R) * h ^ 7 * w1 ^ 4 * e3 * a2 * b6
    - (732130263760896 : R) * h ^ 7 * w1 ^ 4 * e3 * a1 * b7
    - (2514386764431360 : R) * h ^ 7 * w1 ^ 3 * e1n * e3 * a2 * b7

def alignedSquareMuZeroQ8QuotOne610c34 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (1724545105920 : R) * h ^ 7 * w1 ^ 3 * e3 ^ 3 * b7
    + (15640233326936064 : R) * h ^ 7 * w1 ^ 3 * a2 ^ 2 * b6
    + (36493877762850816 : R) * h ^ 7 * w1 ^ 3 * a2 * a1 * b7
    + (35940940220989440 : R) * h ^ 7 * w1 ^ 2 * e1n * a2 ^ 2 * b7
    + (147905103790080 : R) * h ^ 7 * w1 ^ 2 * e3 ^ 2 * a2 * b7
    - (3194750241865728 : R) * h ^ 7 * w1 * e3 * a2 ^ 2 * b7
    + (13270501004673024 : R) * h ^ 7 * a2 ^ 3 * b7
    - (302796245606400 : R) * h ^ 6 * w1 ^ 7 * e1n ^ 3 * b8n
    - (44824301862912 : R) * h ^ 6 * w1 ^ 7 * a0 * b8n
    + (169565897539584 : R) * h ^ 6 * w1 ^ 6 * e1n ^ 2 * e3 * b8n

def alignedSquareMuZeroQ8QuotOne610c35 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (1778030640562176 : R) * h ^ 6 * w1 ^ 6 * e1n * a1 * b8n
    - (7166002278629376 : R) * h ^ 6 * w1 ^ 5 * e1n ^ 2 * a2 * b8n
    - (29489721311232 : R) * h ^ 6 * w1 ^ 5 * e1n * e3 ^ 2 * b8n
    + (418360150720512 : R) * h ^ 6 * w1 ^ 5 * e3 * a1 * b8n
    + (2274921358295040 : R) * h ^ 6 * w1 ^ 4 * e1n * e3 * a2 * b8n
    + (1560302714880 : R) * h ^ 6 * w1 ^ 4 * e3 ^ 3 * b8n
    - (22591448138907648 : R) * h ^ 6 * w1 ^ 4 * a2 * a1 * b8n
    - (38793395794083840 : R) * h ^ 6 * w1 ^ 3 * e1n * a2 ^ 2 * b8n
    - (159643604090880 : R) * h ^ 6 * w1 ^ 3 * e3 ^ 2 * a2 * b8n
    + (4563928916951040 : R) * h ^ 6 * w1 ^ 2 * e3 * a2 ^ 2 * b8n

def alignedSquareMuZeroQ8QuotOne610c36 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (32860288202047488 : R) * h ^ 6 * w1 * a2 ^ 3 * b8n
    - (26372304 : R) * h ^ 5 * w1 ^ 15
    - (3242498688 : R) * h ^ 5 * w1 ^ 10 * b5
    - (1102449553920 : R) * h ^ 5 * w1 ^ 9 * e1n * b6
    - (51319026734976 : R) * h ^ 5 * w1 ^ 8 * e1n ^ 2 * b7
    + (389099842560 : R) * h ^ 5 * w1 ^ 8 * e3 * b6
    + (26066807230464 : R) * h ^ 5 * w1 ^ 7 * e1n * e3 * b7
    - (33618226397184 : R) * h ^ 5 * w1 ^ 7 * a2 * b6
    - (39221264130048 : R) * h ^ 5 * w1 ^ 7 * a1 * b7
    - (1555776810491904 : R) * h ^ 5 * w1 ^ 6 * e1n * a2 * b7

def alignedSquareMuZeroQ8QuotOne610c37 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (3201186852864 : R) * h ^ 5 * w1 ^ 6 * e3 ^ 2 * b7
    + (366065131880448 : R) * h ^ 5 * w1 ^ 5 * e3 * a2 * b7
    - (9883758560772096 : R) * h ^ 5 * w1 ^ 4 * a2 ^ 2 * b7
    + (24980690262528 : R) * h ^ 4 * w1 ^ 9 * e1n ^ 2 * b8n
    - (13033403615232 : R) * h ^ 4 * w1 ^ 8 * e1n * e3 * b8n
    + (14007594332160 : R) * h ^ 4 * w1 ^ 8 * a1 * b8n
    + (804347194540032 : R) * h ^ 4 * w1 ^ 7 * e1n * a2 * b8n
    + (1655035379712 : R) * h ^ 4 * w1 ^ 7 * e3 ^ 2 * b8n
    - (197558960062464 : R) * h ^ 4 * w1 ^ 6 * e3 * a2 * b8n
    + (5647862034726912 : R) * h ^ 4 * w1 ^ 5 * a2 ^ 2 * b8n

def alignedSquareMuZeroQ8QuotOne610c38 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (884317824 : R) * h ^ 3 * w1 ^ 11 * b6
    + (407293862976 : R) * h ^ 3 * w1 ^ 10 * e1n * b7
    - (142910127360 : R) * h ^ 3 * w1 ^ 9 * e3 * b7
    + (12256645040640 : R) * h ^ 3 * w1 ^ 8 * a2 * b7
    - (148106859264 : R) * h ^ 2 * w1 ^ 11 * e1n * b8n
    + (51719855616 : R) * h ^ 2 * w1 ^ 10 * e3 * b8n
    - (4409798215680 : R) * h ^ 2 * w1 ^ 9 * a2 * b8n
    - (243596808 : R) * h * w1 ^ 12 * b7
    + (67814496 : R) * w1 ^ 13 * b8n

set_option maxHeartbeats 1600000000 in
/-- The `μ = 0` `q₈`-peeled jet after cancelling the leading `h`. -/
def alignedSquareMuZeroQ8QuotOne610 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    alignedSquareMuZeroQ8QuotOne610c0 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c1 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c2 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c3 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c4 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c5 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c6 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c7 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c8 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c9 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c10 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c11 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c12 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c13 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c14 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c15 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c16 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c17 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c18 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c19 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c20 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c21 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c22 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c23 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c24 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c25 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c26 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c27 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c28 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c29 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c30 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c31 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c32 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c33 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c34 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c35 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c36 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c37 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 +
    alignedSquareMuZeroQ8QuotOne610c38 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
