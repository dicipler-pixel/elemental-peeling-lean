/-
# Two face forms of the closing test

Ported unchanged (namespace and header only) from `lean/TwoFaceForms.lean` of the v1.1 package.
-/

namespace ElementalPeeling.LoopWall

/-
TwoFaceForms.lean — Claude, for Jeromie Beasley, 21 Nov 2026. Core Lean only, no Mathlib.
Two faces with returned powers x = Γ_a², y = Γ_b² (0 ≤ x, y < 1). sinh² h = Γ²/(1 − Γ²), so the
product form of the closing test, sinh a · sinh b < 1, squared is x·y < (1 − x)(1 − y), and the sum form
is Γ_a² + Γ_b² < 1. At the loop wall the two forms are the same statement (two_face_forms_agree).
At another cutoff they are not: two_face_forms_split_at_midpoint gives one pair, read with the window-midpoint
cutoff, where the sum form calls the loop closed and the product form calls it open.
-/
theorem two_face_identity (x y : Rat) : (1 - x) * (1 - y) - x * y = 1 - (x + y) := by grind

theorem two_face_forms_agree (x y : Rat) : x * y < (1 - x) * (1 - y) ↔ x + y < 1 := by
  have h := two_face_identity x y
  constructor <;> intro h' <;> grind

/-- A cutoff other than the wall: threshold t on each face, t = Γ_c². Product form:
x·y·(1−t)² < t²·(1−x)(1−y); sum form: x + y < 2t. With t = 0.5005 (just above ½) and the pair
x = 0.9999, y = 0.0005, the sum form says closed and the product form says open. -/
theorem two_face_forms_split_at_midpoint :
    ¬ ((9999 / 10000 : Rat) * (5 / 10000) * ((1 - 5005 / 10000) * (1 - 5005 / 10000)) <
        (5005 / 10000) * (5005 / 10000) * ((1 - 9999 / 10000) * (1 - 5 / 10000))) ∧
    ((9999 / 10000 : Rat) + 5 / 10000 < 2 * (5005 / 10000)) := by
  refine ⟨?_, ?_⟩ <;> grind

end ElementalPeeling.LoopWall
