import Grok810NonzeroFaceSplitAssemblySpeedValTrimSpeedSplitPart3Part01Scratch
import Grok810NonzeroFaceSplitAssemblySpeedValTrimSpeedSplitPart3Part02Scratch

/-! # SPEED (tranche 2): declarations moved out of `Grok810NonzeroFaceSplitAssemblySpeedValTrimScratch` so that no
single module retains more than a few large `polyR` unfoldings.
Part 3 of 5.  Statements unchanged. -/

/-! This module is now a pure import aggregator: its declarations live in the
`Part..` modules above, one per file, so that no single module elaborates them
all at once.  Every statement, name, binder and section context is unchanged. -/
