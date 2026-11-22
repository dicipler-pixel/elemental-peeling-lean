import Mathlib

/-!
# Ledger descent: a loop-vanishing ledger is an endpoint potential

Direction D6.  Paths are indexed lists of steps (`Chained G s p t`), so endpoints are part of
the statement.  `walkSum_append`, `walkSum_reverseSteps`, both directions of
`endpointPotential_iff_vanishesOnLoops`, path independence, and the explicit potential
`walkSum_eq_radialPotential_sub`.  Skew symmetry alone is refuted: `chiralWeight` on `Fin 3` has
`chiralWeight_triangle_sum = 3` and `chiralWeight_has_no_potential`; the corrected hypothesis is
the cocycle identity (`walkSum_eq_weight_of_cocycle`).

Written in the second parallel formalization round (swarm `smws2pzvk`, direction m1),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem` so the
repository audit sees it, trailing `#print axioms` lines removed because `scripts/verify.py` audits
every named theorem.  See PROVENANCE.md.
-/

namespace ElementalPeeling.LoopWall.LedgerDescent

universe u v

/-- A vertex type equipped with a symmetric step relation. -/
structure SymRel (V : Type u) where
  Adj : V → V → Prop
  symm : ∀ {s t : V}, Adj s t → Adj t s

namespace SymRel

variable {V : Type u} (G : SymRel V)

/-- A directed edge of a symmetric relation.  Reversing an edge is always possible. -/
structure Step where
  src : V
  dst : V
  adj : G.Adj src dst

/-- The reversed directed edge. -/
def Step.reverse (e : Step G) : Step G where
  src := e.dst
  dst := e.src
  adj := G.symm e.adj

@[simp] theorem Step.reverse_src (e : Step G) : e.reverse.src = e.dst := rfl
@[simp] theorem Step.reverse_dst (e : Step G) : e.reverse.dst = e.src := rfl

/-- `Chained G s p t` says that the list of steps `p` goes from `s` to `t`. -/
inductive Chained : V → List (Step G) → V → Type u
  | nil (s : V) : Chained s [] s
  | cons (e : Step G) {t : V} {p : List (Step G)}
      (rest : Chained e.dst p t) : Chained e.src (e :: p) t

/-- Explicit concatenation of chained lists of steps. -/
def Chained.append {s m t : V} {p q : List (Step G)} :
    Chained G s p m → Chained G m q t → Chained G s (p ++ q) t
  | .nil _, hq => hq
  | .cons e hp, hq => .cons e (hp.append hq)

/-- Reversal of a chained list of steps. -/
def Chained.reverse {s t : V} {p : List (Step G)} :
    Chained G s p t → Chained G t (p.reverse.map (Step.reverse G)) s
  | .nil _ => .nil _
  | .cons e hp => by
      simp only [List.reverse_cons, List.map_append, List.map_singleton]
      exact Chained.append (G := G) (Chained.reverse hp)
        (.cons e.reverse (.nil e.src))

/-- A path is a list of steps, together with its chaining proof and endpoints. -/
structure Path (s t : V) where
  steps : List (Step G)
  chained : Chained G s steps t

/-- The empty path at a vertex. -/
def Path.nil (s : V) : Path G s s where
  steps := []
  chained := .nil s

/-- Explicit append on paths. -/
def Path.append {s m t : V} (p : Path G s m) (q : Path G m t) : Path G s t where
  steps := p.steps ++ q.steps
  chained := Chained.append (G := G) p.chained q.chained

/-- Reverse the order of the steps and reverse every step. -/
def Path.reverse {s t : V} (p : Path G s t) : Path G t s where
  steps := p.steps.reverse.map (Step.reverse G)
  chained := Chained.reverse (G := G) p.chained

/-- A one-step path. -/
def Path.single (e : Step G) : Path G e.src e.dst where
  steps := [e]
  chained := .cons e (.nil e.dst)

end SymRel

open SymRel

variable {V : Type u} {G : SymRel V} {A : Type v} [AddCommGroup A]

/-- The list of steps underlying path reversal. -/
def reverseSteps (p : List (Step G)) : List (Step G) :=
  p.reverse.map (Step.reverse G)

/-- Endpoint dependence: any two paths with the same endpoints have equal ledgers. -/
def EndpointPotential (L : List (Step G) → A) : Prop :=
  ∀ {s t : V} (p q : Path G s t), L p.steps = L q.steps

/-- Vanishing on all closed paths. -/
def VanishesOnLoops (L : List (Step G) → A) : Prop :=
  ∀ {s : V} (p : Path G s s), L p.steps = 0

/-- Additivity on empty paths follows from additivity under concatenation. -/
theorem ledger_empty_eq_zero (L : List (Step G) → A)
    (hAdd : ∀ p q, L (p ++ q) = L p + L q) : L [] = 0 := by
  have h : L [] = L [] + L [] := by
    simpa using hAdd [] []
  have h' : L [] + L [] = L [] + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h'

/-- If every loop has zero ledger, the ledger depends only on the endpoints. -/
theorem endpointPotential_of_vanishesOnLoops (L : List (Step G) → A)
    (hAdd : ∀ p q, L (p ++ q) = L p + L q)
    (hReverse : ∀ p, L (reverseSteps p) = -L p)
    (hLoops : VanishesOnLoops L) : EndpointPotential L := by
  intro s t p q
  have h := hLoops (Path.append (G := G) p (Path.reverse (G := G) q))
  change L (p.steps ++ reverseSteps q.steps) = 0 at h
  rw [hAdd, hReverse] at h
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg] using h

/-- Conversely, endpoint dependence forces every closed path to have zero ledger. -/
theorem vanishesOnLoops_of_endpointPotential (L : List (Step G) → A)
    (hAdd : ∀ p q, L (p ++ q) = L p + L q)
    (hEndpoints : EndpointPotential L) : VanishesOnLoops L := by
  intro s p
  calc
    L p.steps = L (Path.nil (G := G) s).steps :=
      hEndpoints p (Path.nil (G := G) s)
    _ = 0 := ledger_empty_eq_zero L hAdd

/-- The loop-wall descent criterion for an additive, reversal-antisymmetric ledger. -/
theorem endpointPotential_iff_vanishesOnLoops (L : List (Step G) → A)
    (hAdd : ∀ p q, L (p ++ q) = L p + L q)
    (hReverse : ∀ p, L (reverseSteps p) = -L p) :
    EndpointPotential L ↔ VanishesOnLoops L :=
  ⟨vanishesOnLoops_of_endpointPotential L hAdd,
    endpointPotential_of_vanishesOnLoops L hAdd hReverse⟩

/-! ## Walk weights on the complete graph -/

/-- The complete symmetric relation; loops at a vertex are allowed. -/
def complete (V : Type u) : SymRel V where
  Adj _ _ := True
  symm h := h

/-- A step between any two vertices of the complete graph. -/
def completeStep (s t : V) : Step (complete V) where
  src := s
  dst := t
  adj := trivial

@[simp] theorem completeStep_src (s t : V) : (completeStep s t).src = s := rfl
@[simp] theorem completeStep_dst (s t : V) : (completeStep s t).dst = t := rfl

/-- Add the weights of the directed steps in a list. -/
def walkSum (w : V → V → A) : List (Step (complete V)) → A
  | [] => 0
  | e :: p => w e.src e.dst + walkSum w p

@[simp] theorem walkSum_nil (w : V → V → A) : walkSum w [] = 0 := rfl
@[simp] theorem walkSum_cons (w : V → V → A) (e : Step (complete V)) p :
    walkSum w (e :: p) = w e.src e.dst + walkSum w p := rfl

theorem walkSum_append (w : V → V → A) (p q : List (Step (complete V))) :
    walkSum w (p ++ q) = walkSum w p + walkSum w q := by
  induction p with
  | nil => simp
  | cons e p ih => simp [ih, add_assoc]

/-- Skew-symmetric weights give a reversal-antisymmetric walk ledger. -/
theorem walkSum_reverseSteps (w : V → V → A)
    (hSkew : ∀ s t, w s t + w t s = 0) (p : List (Step (complete V))) :
    walkSum w (reverseSteps p) = -walkSum w p := by
  induction p with
  | nil => simp [reverseSteps]
  | cons e p ih =>
      have hrev : w e.dst e.src = -w e.src e.dst := by
        exact eq_neg_of_add_eq_zero_left (hSkew e.dst e.src)
      have hcons : reverseSteps (e :: p) = reverseSteps p ++ [e.reverse] := by
        simp [reverseSteps]
      rw [hcons, walkSum_append, ih]
      simp only [walkSum_cons, walkSum_nil, add_zero, Step.reverse_src, Step.reverse_dst]
      rw [hrev]
      abel

/-- The explicit triangular closed path `s → t → r → s`. -/
def trianglePath (s t r : V) : Path (complete V) s s where
  steps := [completeStep s t, completeStep t r, completeStep r s]
  chained := Chained.cons (completeStep s t)
    (Chained.cons (completeStep t r)
      (Chained.cons (completeStep r s) (Chained.nil s)))

/-- In zero-loop case, the walk sum of every path is the weight of its direct step. -/
theorem walkSum_eq_direct_of_vanishesOnLoops (w : V → V → A)
    (hSkew : ∀ s t, w s t + w t s = 0)
    (hLoops : VanishesOnLoops (walkSum w)) {s t : V}
    (p : Path (complete V) s t) : walkSum w p.steps = w s t := by
  have hEndpoints : EndpointPotential (walkSum w) :=
    endpointPotential_of_vanishesOnLoops (walkSum w)
      (walkSum_append w) (walkSum_reverseSteps w hSkew) hLoops
  calc
    walkSum w p.steps =
        walkSum w (Path.single (G := complete V) (completeStep s t)).steps :=
      hEndpoints p (Path.single (G := complete V) (completeStep s t))
    _ = w s t := by simp [Path.single]

/-- The potential determined by a root vertex. -/
def radialPotential (w : V → V → A) (r i : V) : A := w r i

/--
Corrected complete-graph theorem: skew-symmetry **and zero on loops** imply
telescoping.  Skew-symmetry alone is refuted below.
-/
theorem walkSum_eq_radialPotential_sub (w : V → V → A)
    (hSkew : ∀ s t, w s t + w t s = 0)
    (hLoops : VanishesOnLoops (walkSum w)) (r : V) {s t : V}
    (p : Path (complete V) s t) :
    walkSum w p.steps = radialPotential w r t - radialPotential w r s := by
  rw [walkSum_eq_direct_of_vanishesOnLoops w hSkew hLoops p]
  have htri : w r s + w s t + w t r = 0 := by
    have h := hLoops (trianglePath r s t)
    simpa [trianglePath, walkSum, add_assoc] using h
  have htr : w t r = -w r t := by
    exact eq_neg_of_add_eq_zero_left (hSkew t r)
  rw [htr] at htri
  apply eq_of_sub_eq_zero
  calc
    w s t - (radialPotential w r t - radialPotential w r s) =
        w r s + w s t + -w r t := by
          simp only [radialPotential]
          abel
    _ = 0 := htri

/-- The corrected telescoping statement specialized to `Fin n`. -/
theorem fin_walkSum_eq_radialPotential_sub {n : ℕ} (w : Fin n → Fin n → A)
    (hSkew : ∀ s t, w s t + w t s = 0)
    (hLoops : VanishesOnLoops (walkSum w)) (r : Fin n) {s t : Fin n}
    (p : Path (complete (Fin n)) s t) :
    walkSum w p.steps = radialPotential w r t - radialPotential w r s :=
  walkSum_eq_radialPotential_sub w hSkew hLoops r p

/-- A compact cocycle hypothesis that directly gives the zero-loop correction. -/
def WeightCocycle (w : V → V → A) : Prop :=
  ∀ s t r, w s t + w t r = w s r

theorem walkSum_chained_eq_weight_of_cocycle (w : V → V → A)
    (hCocycle : WeightCocycle w) {s t : V} {p : List (Step (complete V))}
    (hp : Chained (complete V) s p t) : walkSum w p = w s t := by
  induction hp with
  | nil s =>
      have h : w s s + w s s = w s s + 0 := by
        rw [add_zero]
        exact hCocycle s s s
      have hz : w s s = 0 := add_left_cancel h
      simp [hz]
  | cons e rest ih =>
      rw [walkSum_cons, ih]
      exact hCocycle e.src e.dst _

theorem walkSum_eq_weight_of_cocycle (w : V → V → A)
    (hCocycle : WeightCocycle w) {s t : V} (p : Path (complete V) s t) :
    walkSum w p.steps = w s t :=
  walkSum_chained_eq_weight_of_cocycle w hCocycle p.chained

/-! ## Why skew-symmetry alone is insufficient -/

/-- Cyclic weights on three vertices: `0 → 1 → 2 → 0` all have weight `1`. -/
def chiralWeight (i j : Fin 3) : ℤ :=
  ![![0, 1, -1], ![-1, 0, 1], ![1, -1, 0]] i j

theorem chiralWeight_skew (i j : Fin 3) :
    chiralWeight i j + chiralWeight j i = 0 := by
  fin_cases i <;> fin_cases j <;> decide

/-- The nonstationary cyclic triangle has nonzero ledger. -/
theorem chiralWeight_triangle_sum :
    walkSum chiralWeight (trianglePath (0 : Fin 3) 1 2).steps = 3 := by
  norm_num [chiralWeight, trianglePath, walkSum]

/-- No potential can telescope this skew-symmetric ledger: its triangle has sum `3`. -/
theorem chiralWeight_has_no_potential :
    ¬∃ potential : Fin 3 → ℤ,
      ∀ {s t : Fin 3} (p : Path (complete (Fin 3)) s t),
        walkSum chiralWeight p.steps = potential t - potential s := by
  rintro ⟨potential, h⟩
  have htri := h (trianglePath 0 1 2)
  rw [chiralWeight_triangle_sum] at htri
  norm_num at htri


end ElementalPeeling.LoopWall.LedgerDescent
