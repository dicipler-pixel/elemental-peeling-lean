import Hypersurface
-- Deliberately false: successful acceptance would invalidate the verification run.
example : 0 ≤ Hypersurface.incrementalForm 1 3 1 (-1) := by
  norm_num [Hypersurface.incrementalForm]
