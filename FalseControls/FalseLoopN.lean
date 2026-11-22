import Mathlib
import LoopWall.Elements
-- Deliberately false: the helium-core opening of nitrogen is inside the loop wall
-- (552.06741 / 97.8901 = 5.6396...), so this control must be rejected.
example : ElementalPeeling.LoopWall.outside (552.06741 / 97.8901) := by
  unfold ElementalPeeling.LoopWall.outside
  constructor <;> norm_num
