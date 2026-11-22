import Mathlib
import LoopWall.Archive
-- Deliberately false: the archive has eight ordinary steps outside the wall, not seven.
example : ElementalPeeling.LoopWall.ordinaryOutside.length = 7 := by
  simp [ElementalPeeling.LoopWall.ordinaryOutside]
