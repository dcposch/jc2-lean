import Grok810ScaleZeroQuarticChamberFacesPart0Scratch
import Grok810ScaleZeroQuarticChamberFacesPart1Scratch
import Grok810ScaleZeroQuarticChamberFacesPart2Scratch
import Grok810ScaleZeroQuarticChamberFacesPart3Scratch
import Grok810ScaleZeroQuarticChamberFacesPart4Scratch
import Grok810ScaleZeroQuarticChamberFacesPart5Scratch
import Grok810ScaleZeroQuarticChamberFacesPart6Scratch
import Grok810ScaleZeroQuarticChamberFacesPart7Scratch
import Grok810ScaleZeroQuarticChamberFacesPart8Scratch
import Grok810ScaleZeroQuarticChamberFacesPart9Scratch
import Grok810ScaleZeroQuarticChamberFacesPart10Scratch

/-! # Cost-argmin faces and rests, `(8,10)` scale zero — aggregator

The single 19,969-line module this replaces was correct but hit the
six-hour compile ceiling, and every later module waits on it.  The
content now lives in
`…FacesPart0Scratch` (the four carriers' load-free part, their eight
load columns and the split identities), `…FacesPart1Scratch` (the
79 packet faces, rests and packet split identities) and
`…FacesPart2..Part10Scratch` (655 load-free rest bounds, ≤ 80
`compute_degree` calls each).  Part 0 → Part 1 is the only dependency
between parts; the bound parts are mutually independent and gate in
parallel.  This module only re-exports them, so modules 10-40 need no
change.  Untracked working note.
-/
