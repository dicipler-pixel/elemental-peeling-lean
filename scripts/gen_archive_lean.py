#!/usr/bin/env python3
# SCRIPT: VOTKP-LOOPWALL-ARCHIVE-01
"""Generate LoopWall/Archive.lean from data/H_to_At_thresholds.csv.

The archive carries every removal threshold from hydrogen to astatine and, for each row, the
ratio `z` of that threshold to the next removal energy of the same element.  Two kinds of row
carry a comparison:

  IE  an ordinary peel step, IE(k+1)/IE(k), for k >= 1
  EA  the anion rung, IE(1)/EA, for the elements with an adopted electron affinity

The generated module does not restate the CSV's own wall column: it recomputes the classification
from the rational `z` alone with the loop-wall predicate `outside`, and lets the kernel check the
counts and the two cutoff windows.

Run:  python3 scripts/gen_archive_lean.py
"""
from __future__ import annotations

import csv
import pathlib
from fractions import Fraction as F

ROOT = pathlib.Path(__file__).resolve().parents[1]
CSV = ROOT / "data" / "H_to_At_thresholds.csv"
OUT = ROOT / "LoopWall" / "Archive.lean"

# The two windows quoted in the paper, as exact decimals: the largest inside value and the
# smallest outside value of each family.  The interval between them is exactly the set of
# cutoffs that reproduces that family's classification.
ORD_A, ORD_B = "5.639665400281", "5.947100834227"    # N helium-core opening / Cs xenon-core opening
AN_A, AN_B = "5.80790205984", "5.866538776091"       # Ag anion rung / Si anion rung


def is_outside(z: str) -> bool:
    """The wall predicate on the exact decimal: 3 < z and 8 < (z - 3)^2."""
    q = F(z)
    return 3 < q and 8 < (q - 3) ** 2


def load():
    ordinary, anion = [], []
    for row in csv.DictReader(CSV.open()):
        z = row["z"].strip()
        if not z:
            continue
        item = (row["symbol"], row["k"], row["kind"], z)
        (ordinary if row["kind"] == "IE" else anion).append(item)
    return ordinary, anion


def load_cn():
    """The carbon and nitrogen helium-core openings, with their propagated intervals.

    The paper's mixed two-face construction couples the carbon core face to the nitrogen core
    face; the row is the last removal above the 1s core followed by the first removal from it.
    """
    rows = [r for r in csv.DictReader(CSV.open()) if r["z"].strip()]
    def pick(sym):
        hits = [r for r in rows if r["symbol"] == sym and r["kind"] == "IE"
                and F(r["z"]) > 5 and F(r["z"]) < 7 and r["z_lower"].strip()]
        assert len(hits) == 1, (sym, len(hits))
        return hits[0]["z"], hits[0]["z_lower"], hits[0]["z_upper"]
    return pick("C"), pick("N")


def load_boxes():
    """The ratio rectangle of every comparison that carries two quoted widths."""
    boxes = []
    for row in csv.DictReader(CSV.open()):
        lo, hi = row["z_lower"].strip(), row["z_upper"].strip()
        if row["z"].strip() and lo and hi:
            boxes.append((lo, hi))
    return boxes


def lean_list(xs, per_line=6):
    """A Lean list literal body, wrapped six items to a line."""
    out, line = [], []
    for x in xs:
        line.append(f"({x} : ℚ)")
        if len(line) == per_line:
            out.append("    " + ", ".join(line) + ",")
            line = []
    if line:
        out.append("    " + ", ".join(line) + ",")
    return "\n" + "\n".join(out)


def main() -> None:
    ordinary, anion = load()
    outside_ord = [i for i in ordinary if is_outside(i[3])]
    inside_ord = [i for i in ordinary if not is_outside(i[3])]
    outside_an = [i for i in anion if is_outside(i[3])]
    inside_an = [i for i in anion if not is_outside(i[3])]
    # For the doc comments only: increasing order.
    outside_ord_sorted = sorted(outside_ord, key=lambda i: F(i[3]))
    outside_an_sorted = sorted(outside_an, key=lambda i: F(i[3]))

    assert len(ordinary) == 3570 and len(outside_ord) == 8, (len(ordinary), len(outside_ord))
    assert len(anion) == 67 and len(outside_an) == 55, (len(anion), len(outside_an))
    assert max(F(i[3]) for i in inside_ord) == F(ORD_A)
    assert min(F(i[3]) for i in outside_ord) == F(ORD_B)
    assert max(F(i[3]) for i in inside_an) == F(AN_A)
    assert min(F(i[3]) for i in outside_an) == F(AN_B)

    (c_z, c_lo, c_hi), (n_z, n_lo, n_hi) = load_cn()
    boxes = load_boxes()
    assert len(boxes) == 3614, len(boxes)

    def q(v):
        r = F(v)
        return r * r - 6 * r + 1

    n_neg = sum(1 for lo, hi in boxes if q(lo) < 0 and q(hi) < 0)
    n_pos = sum(1 for lo, hi in boxes if q(lo) > 0 and q(hi) > 0 and (3 < F(lo) or F(hi) < 3))
    assert n_neg + n_pos == len(boxes), (n_neg, n_pos)
    assert all(F(lo) <= F(hi) for lo, hi in boxes)

    ord_doc = "\n".join(f"  {sym}{k} — z = {z}" for sym, k, _, z in outside_ord_sorted)
    an_doc = "\n".join(f"  {sym} — z = {z}" for sym, _, _, z in outside_an_sorted)

    boxes_list = "\n".join(
        "    " + ", ".join(f"({lo}, {hi})" for lo, hi in boxes[i:i + 4]) + ","
        for i in range(0, len(boxes), 4))

    text = f"""import Mathlib
import LoopWall.Elements

/-!
# The archive certificate: {len(ordinary)} ordinary steps and {len(anion)} anion rungs

GENERATED by `scripts/gen_archive_lean.py` from `data/H_to_At_thresholds.csv`; do not edit by
hand.  Every number below is the exact decimal of the archive, read as a rational, so the
comparisons the kernel makes are the arithmetic the paper reports, without rounding.

The CSV's own wall column is not used.  Each row is classified again from `z` alone by the
loop-wall predicates of `LoopWall.Elements`, and the kernel checks the recount:

  * {len(ordinary)} ordinary adjacent steps, {len(outside_ord)} outside the wall;
  * {len(anion)} scored anion rungs, {len(outside_an)} outside and {len(inside_an)} inside;
  * every ordinary step is at most {ORD_A} or at least {ORD_B}, so every rational cutoff in
    `[{ORD_A}, {ORD_B})` selects exactly the same {len(outside_ord)} ordinary steps;
  * every anion rung is at most {AN_A} or at least {AN_B}, so every cutoff in
    `[{AN_A}, {AN_B})` selects exactly the same {len(outside_an)} rungs.

What is *not* certified here: that the archive values are the true ionization energies, that the
grades in the CSV are the right ones, or that a `z` is a "core opening" in any physical sense.
The module certifies the arithmetic of the table, nothing about the world.

The window endpoints are the largest inside and the smallest outside value of each family.  The
paper quotes silver's rung rounded ({AN_A} -> 5.8079020598); the exact decimal is used here,
because a rounded-down endpoint would exclude silver from its own window.
-/

set_option maxRecDepth 200000

namespace ElementalPeeling.LoopWall

/-- `outside`, as a Boolean, so that a filter over thousands of rationals can be decided by the
kernel.  `outside_iff_b` says the two agree. -/
abbrev outsideB (z : ℚ) : Bool := decide (3 < z ∧ 8 < (z - 3) * (z - 3))

/-- `inside`, as a Boolean. -/
abbrev insideB (z : ℚ) : Bool := decide (1 < z ∧ (z - 3) * (z - 3) < 8)

theorem outside_iff_b (z : ℚ) : outside z ↔ outsideB z = true := by
  unfold outside; simp [outsideB]

theorem inside_iff_b (z : ℚ) : inside z ↔ insideB z = true := by
  unfold inside; simp [insideB]

/-! ## The two windows, as arithmetic -/

/-- Below the ordinary window nothing of the archive is outside the wall. -/
theorem outsideB_false_of_le {{z : ℚ}} (h₁ : 1 < z) (h₂ : z ≤ {ORD_A}) : outsideB z = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [outsideB, decide_eq_true_eq] at h
  nlinarith [h.2, h.1, sq_nonneg (z - {ORD_A})]

/-- Above the ordinary window everything of the archive is outside the wall. -/
theorem outsideB_true_of_ge {{z : ℚ}} (h : {ORD_B} ≤ z) : outsideB z = true := by
  simp only [outsideB, decide_eq_true_eq]
  constructor <;> nlinarith

/-- Below the anion window nothing of the archive is outside the wall. -/
theorem outsideB_false_of_le_anion {{z : ℚ}} (h₁ : 1 < z) (h₂ : z ≤ {AN_A}) :
    outsideB z = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [outsideB, decide_eq_true_eq] at h
  nlinarith [h.2, h.1, sq_nonneg (z - {AN_A})]

/-- Above the anion window everything of the archive is outside the wall. -/
theorem outsideB_true_of_ge_anion {{z : ℚ}} (h : {AN_B} ≤ z) : outsideB z = true := by
  simp only [outsideB, decide_eq_true_eq]
  constructor <;> nlinarith

/-! ## The archive, as exact rationals -/

/-- The {len(ordinary)} ordinary adjacent peel steps IE(k+1)/IE(k), in archive order
(hydrogen to astatine; the lanthanide row follows caesium). -/
def ordinarySteps : List ℚ := [{lean_list([i[3] for i in ordinary])}]

/-- The {len(anion)} scored anion rungs IE(1)/EA, in archive order. -/
def anionRungs : List ℚ := [{lean_list([i[3] for i in anion])}]

/-- The {len(outside_ord)} ordinary steps outside the wall, in increasing order:

{ord_doc}
-/
def ordinaryOutside : List ℚ := [{lean_list([i[3] for i in outside_ord_sorted])}]

/-- The {len(outside_an)} anion rungs outside the wall, in increasing order:

{an_doc}
-/
def anionOutside : List ℚ := [{lean_list([i[3] for i in outside_an_sorted])}]

/-! ## The kernel recount -/

/-- Exactly {len(outside_ord)} of the {len(ordinary)} ordinary steps lie outside the wall. -/
theorem ordinary_count : (ordinarySteps.filter outsideB).length = {len(outside_ord)} := by
  decide +kernel

/-- Exactly {len(outside_an)} of the {len(anion)} anion rungs lie outside the wall. -/
theorem anion_outside_count : (anionRungs.filter outsideB).length = {len(outside_an)} := by
  decide +kernel

/-- Exactly {len(inside_an)} of the {len(anion)} anion rungs lie inside the wall. -/
theorem anion_inside_count : (anionRungs.filter insideB).length = {len(inside_an)} := by
  decide +kernel

theorem ordinaryOutside_length : ordinaryOutside.length = {len(outside_ord)} := by
  decide +kernel

theorem anionOutside_length : anionOutside.length = {len(outside_an)} := by
  decide +kernel

theorem ordinarySteps_length : ordinarySteps.length = {len(ordinary)} := by
  decide +kernel

theorem anionRungs_length : anionRungs.length = {len(anion)} := by
  decide +kernel

/-- Every ordinary step is a genuine peel step: the higher threshold is the larger one. -/
theorem ordinary_one_lt : ordinarySteps.all (fun z => decide (1 < z)) = true := by
  decide +kernel

/-- No ordinary step lies strictly between the two window endpoints. -/
theorem ordinary_dichotomy :
    ordinarySteps.all (fun z => decide (z ≤ {ORD_A}) || decide ({ORD_B} ≤ z)) = true := by
  decide +kernel

theorem anion_one_lt : anionRungs.all (fun z => decide (1 < z)) = true := by
  decide +kernel

/-- No anion rung lies strictly between the two window endpoints. -/
theorem anion_dichotomy :
    anionRungs.all (fun z => decide (z ≤ {AN_A}) || decide ({AN_B} ≤ z)) = true := by
  decide +kernel

/-! ## The cutoff windows -/

/-- **The ordinary cutoff window.**  Every rational cutoff `c` in `[{ORD_A}, {ORD_B})` classifies
each of the {len(ordinary)} ordinary steps exactly as the loop wall does.  Since
`3 + 2√2 = 5.828427…` lies inside this interval, the archive cannot distinguish the wall from any
other cutoff in it: the value is fixed by the equal-face construction, not by this table. -/
theorem ordinary_cutoff_window (c : ℚ) (h₁ : {ORD_A} ≤ c) (h₂ : c < {ORD_B}) :
    ordinarySteps.filter (fun z => decide (c < z)) = ordinarySteps.filter outsideB := by
  apply List.filter_congr
  intro z hz
  have h1z : 1 < z := by
    have h := List.all_eq_true.mp ordinary_one_lt z hz
    simpa using h
  have hd : z ≤ {ORD_A} ∨ {ORD_B} ≤ z := by
    have h := List.all_eq_true.mp ordinary_dichotomy z hz
    rcases Bool.or_eq_true .. ▸ h with h' | h'
    · exact Or.inl (by simpa using h')
    · exact Or.inr (by simpa using h')
  rcases hd with hle | hge
  · rw [outsideB_false_of_le h1z hle]
    simp [not_lt.mpr (le_trans hle h₁)]
  · rw [outsideB_true_of_ge hge]
    simp [lt_of_lt_of_le h₂ hge]

/-- The count consequence: every cutoff in the window selects exactly {len(outside_ord)} steps. -/
theorem ordinary_cutoff_count (c : ℚ) (h₁ : {ORD_A} ≤ c) (h₂ : c < {ORD_B}) :
    (ordinarySteps.filter (fun z => decide (c < z))).length = {len(outside_ord)} := by
  rw [ordinary_cutoff_window c h₁ h₂]
  exact ordinary_count

/-- **The anion cutoff window.**  The same statement for the {len(anion)} anion rungs. -/
theorem anion_cutoff_window (c : ℚ) (h₁ : {AN_A} ≤ c) (h₂ : c < {AN_B}) :
    anionRungs.filter (fun z => decide (c < z)) = anionRungs.filter outsideB := by
  apply List.filter_congr
  intro z hz
  have h1z : 1 < z := by
    have h := List.all_eq_true.mp anion_one_lt z hz
    simpa using h
  have hd : z ≤ {AN_A} ∨ {AN_B} ≤ z := by
    have h := List.all_eq_true.mp anion_dichotomy z hz
    rcases Bool.or_eq_true .. ▸ h with h' | h'
    · exact Or.inl (by simpa using h')
    · exact Or.inr (by simpa using h')
  rcases hd with hle | hge
  · rw [outsideB_false_of_le_anion h1z hle]
    simp [not_lt.mpr (le_trans hle h₁)]
  · rw [outsideB_true_of_ge_anion hge]
    simp [lt_of_lt_of_le h₂ hge]

theorem anion_cutoff_count (c : ℚ) (h₁ : {AN_A} ≤ c) (h₂ : c < {AN_B}) :
    (anionRungs.filter (fun z => decide (c < z))).length = {len(outside_an)} := by
  rw [anion_cutoff_window c h₁ h₂]
  exact anion_outside_count

/-! ## The error rectangles: no comparison crosses the wall

The paper also reports that when both quoted widths are propagated, the resulting ratio interval
stays on one side of the wall for every comparison.  `q z = z^2 - 6z + 1` is the wall quadratic:
`q z < 0` is inside, `q z > 0` with `z > 3` is outside.  The two interval lemmas below turn the
endpoint checks into a statement about the whole rectangle, and `ratioBoxes_no_crossing` is the
kernel check that every endpoint pair satisfies one of them.
-/

/-- The wall quadratic. -/
abbrev q (z : ℚ) : ℚ := z * z - 6 * z + 1

theorem q_neg_of_ends_neg {{a b z : ℚ}} (haz : a ≤ z) (hzb : z ≤ b)
    (ha : q a < 0) (hb : q b < 0) : q z < 0 := by
  have hsq : (z - 3) ^ 2 < 8 := by
    nlinarith [ha, hb, haz, hzb, sq_nonneg (z - a), sq_nonneg (b - z),
      mul_nonneg (sub_nonneg.mpr haz) (sub_nonneg.mpr hzb)]
  nlinarith [hsq]

theorem q_pos_of_ends_pos {{a b z : ℚ}} (haz : a ≤ z) (hzb : z ≤ b)
    (ha : 0 < q a) (hb : 0 < q b) (hside : 3 < a ∨ b < 3) : 0 < q z := by
  have hsq : 8 < (z - 3) ^ 2 := by
    rcases hside with h | h
    · nlinarith [ha, haz, h]
    · nlinarith [hb, hzb, h]
  nlinarith [hsq]

/-- The ratio rectangle of every comparison that carries two quoted widths, as
`(z_lower, z_upper)`, in archive order. -/
def ratioBoxes : List (ℚ × ℚ) := [{boxes_list}]

/-- A rectangle is safe when the wall quadratic has one sign on it. -/
abbrev boxOK (p : ℚ × ℚ) : Bool :=
  decide (q p.1 < 0 ∧ q p.2 < 0) ||
    decide (0 < q p.1 ∧ 0 < q p.2 ∧ (3 < p.1 ∨ p.2 < 3))

theorem ratioBoxes_length : ratioBoxes.length = {len(boxes)} := by decide +kernel

/-- Every one of the {len(boxes)} rectangles satisfies an endpoint test. -/
theorem ratioBoxes_ok : ratioBoxes.all boxOK = true := by decide +kernel

/-- **No rectangle crosses the wall.**  For every comparison with two quoted widths, the wall
quadratic has a single sign on the whole propagated interval, so the classification of the central
value is stable across the rectangle. -/
theorem ratioBoxes_no_crossing (p : ℚ × ℚ) (hp : p ∈ ratioBoxes) :
    (∀ z ∈ Set.Icc p.1 p.2, q z < 0) ∨ (∀ z ∈ Set.Icc p.1 p.2, 0 < q z) := by
  have hb := List.all_eq_true.mp ratioBoxes_ok p hp
  rcases Bool.or_eq_true .. ▸ hb with h | h
  · have h' : q p.1 < 0 ∧ q p.2 < 0 := by simpa using h
    exact Or.inl fun z hz => q_neg_of_ends_neg hz.1 hz.2 h'.1 h'.2
  · have h' : 0 < q p.1 ∧ 0 < q p.2 ∧ (3 < p.1 ∨ p.2 < 3) := by simpa using h
    exact Or.inr fun z hz => q_pos_of_ends_pos hz.1 hz.2 h'.1 h'.2.1 h'.2.2

/-- The two-face margin is increasing in each ratio: `Γ` is increasing on the rising side and
nonnegative there, so the margin is at its smallest at the lower ends of the two intervals. -/
theorem gam_mono {{a b : ℚ}} (h1 : 1 < a) (hab : a ≤ b) : gam a ≤ gam b := by
  unfold gam
  have ha : 0 < a + 1 := by grind
  have hb : 0 < b + 1 := by grind
  rw [div_le_div_iff₀ ha hb]
  grind

theorem gam_nonneg {{a : ℚ}} (h1 : 1 ≤ a) : 0 ≤ gam a := by
  unfold gam
  have h : 0 < a + 1 := by grind
  exact div_nonneg (by grind) (by grind)

theorem gam_sq_mono {{a b : ℚ}} (h1 : 1 < a) (hab : a ≤ b) : gam a ^ 2 ≤ gam b ^ 2 := by
  have h0 := gam_nonneg (le_of_lt h1)
  have h := gam_mono h1 hab
  nlinarith

/-- **The carbon/nitrogen mixed two-face margin is positive, across both input rectangles.**
With the carbon helium-core opening and the nitrogen helium-core opening as the two faces
`Γ_C`, `Γ_N`, the margin `Γ_C² + Γ_N² − 1` is approximately `0.00309334` at the central values and
stays positive for every ratio in the two propagated intervals. Only the lower endpoints are
needed: `gam` is monotone and the margin increases in both ratios, so the two upper bounds would
be hypotheses the proof never uses, and the theorem is stated without them. -/
theorem twoFace_margin_C_N (zc zn : ℚ)
    (hc1 : {c_lo} ≤ zc)
    (hn1 : {n_lo} ≤ zn) :
    0 < gam zc ^ 2 + gam zn ^ 2 - 1 := by
  have hcl : gam {c_lo} ^ 2 ≤ gam zc ^ 2 :=
    gam_sq_mono (by norm_num) hc1
  have hnl : gam {n_lo} ^ 2 ≤ gam zn ^ 2 :=
    gam_sq_mono (by norm_num) hn1
  have hbase : 0 < gam {c_lo} ^ 2 + gam {n_lo} ^ 2 - 1 := by
    unfold gam
    norm_num
  linarith

/-- The central values give the paper's quoted margin, up to the printed precision: the exact
rational is `0.0030933375660…`, and the paper prints `0.00309334`. -/
theorem twoFace_margin_C_N_central :
    0.00309333 < gam {c_z} ^ 2 + gam {n_z} ^ 2 - 1 ∧
      gam {c_z} ^ 2 + gam {n_z} ^ 2 - 1 < 0.00309334 := by
  unfold gam
  constructor <;> norm_num

end ElementalPeeling.LoopWall
"""
    OUT.write_text(text)
    print(f"wrote {OUT.relative_to(ROOT)}: {len(ordinary)} ordinary, {len(anion)} anion rungs")


if __name__ == "__main__":
    main()
