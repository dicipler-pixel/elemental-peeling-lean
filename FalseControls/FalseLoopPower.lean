import Mathlib
import LoopWall.Elements
-- Deliberately false: reversal keeps the returned power Γ², so it cannot flip its sign.
-- At z = 2 both orders give 1/9; a ledger that reversed the sign of Γ² would demand −1/9.
example : ElementalPeeling.LoopWall.gam (1 / 2) * ElementalPeeling.LoopWall.gam (1 / 2) =
    - (ElementalPeeling.LoopWall.gam 2 * ElementalPeeling.LoopWall.gam 2) := by
  norm_num [ElementalPeeling.LoopWall.gam]
