import Mathlib
import LoopWall.Elements
-- Deliberately false: the helium-core opening of carbon is outside the loop wall
-- (392.09056 / 64.49352 = 6.0795...), so this control must be rejected.
example : ElementalPeeling.LoopWall.inside (392.09056 / 64.49352) := by
  unfold ElementalPeeling.LoopWall.inside
  constructor <;> norm_num
