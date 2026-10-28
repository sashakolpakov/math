import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Shared interfaces for sparse ternary parity checks

The definitions distinguish edge coordinates from graph vertices. Parallel
edges have different ports. All construction theorems built on these interfaces
must eventually discharge the local-distance and graph-mixing hypotheses.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

abbrev F3 := ZMod 3

abbrev CheckMatrix (R C : Type*) := Matrix R C F3

section Words

variable {C R : Type*} [Fintype C]

def support (w : C → F3) : Finset C :=
  Finset.univ.filter fun c => w c ≠ 0

def weight (w : C → F3) : ℕ := (support w).card

theorem weight_eq_sum (w : C → F3) :
    weight w = ∑ c, if w c ≠ 0 then 1 else 0 := by
  simp [weight, support, Finset.card_filter]

@[simp] theorem mem_support (w : C → F3) (c : C) :
    c ∈ support w ↔ w c ≠ 0 := by
  simp [support]

@[simp] theorem support_zero : support (0 : C → F3) = ∅ := by
  simp [support]

@[simp] theorem weight_zero : weight (0 : C → F3) = 0 := by
  simp [weight]

theorem weight_le_card (w : C → F3) : weight w ≤ Fintype.card C := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

@[simp] theorem weight_eq_zero_iff (w : C → F3) : weight w = 0 ↔ w = 0 := by
  simp only [weight, Finset.card_eq_zero]
  constructor
  · intro h
    funext c
    by_contra hc
    have : c ∈ support w := (mem_support w c).2 hc
    simp [h] at this
  · intro h
    simp [h]

theorem weight_pos_iff (w : C → F3) : 0 < weight w ↔ w ≠ 0 := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, weight_eq_zero_iff]

def check (Q : CheckMatrix R C) (w : C → F3) (r : R) : F3 :=
  ∑ c, Q r c * w c

def IsCodeword (Q : CheckMatrix R C) (w : C → F3) : Prop :=
  ∀ r, check Q w r = 0

def HasDistance (Q : CheckMatrix R C) (d : ℕ) : Prop :=
  ∀ w, IsCodeword Q w → w ≠ 0 → d ≤ weight w

def HasRelativeDistance (Q : CheckMatrix R C) (δ : ℝ) : Prop :=
  ∀ w, IsCodeword Q w → w ≠ 0 → δ * Fintype.card C ≤ (weight w : ℝ)

@[simp] theorem check_zero (Q : CheckMatrix R C) (r : R) :
    check Q 0 r = 0 := by
  simp [check]

theorem zero_isCodeword (Q : CheckMatrix R C) : IsCodeword Q 0 := by
  intro r
  simp

def rowSupport (Q : CheckMatrix R C) (r : R) : Finset C := support (Q r)

def columnSupport [Fintype R] (Q : CheckMatrix R C) (c : C) : Finset R :=
  support fun r => Q r c

theorem rowSupport_card_le (Q : CheckMatrix R C) (r : R) :
    (rowSupport Q r).card ≤ Fintype.card C := weight_le_card (Q r)

omit [Fintype C] in
theorem columnSupport_card_le [Fintype R] (Q : CheckMatrix R C) (c : C) :
    (columnSupport Q c).card ≤ Fintype.card R := weight_le_card (fun r => Q r c)

end Words

/-- A regular bipartite graph represented by its bijection of left and right
ports. Edges are left ports. No simplicity assumption is made. -/
structure PortGraph (V P : Type*) where
  rotation : (V × P) ≃ (V × P)

namespace PortGraph

variable {V P : Type*} [Fintype V] [Fintype P] [DecidableEq V]

def leftWord (w : V × P → F3) (v : V) : P → F3 := fun p => w (v, p)

def rightWord (G : PortGraph V P) (w : V × P → F3) (v : V) : P → F3 :=
  fun p => w (G.rotation.symm (v, p))

def edgesBetween (G : PortGraph V P) (U W : Finset V) : Finset (V × P) :=
  Finset.univ.filter fun e => e.1 ∈ U ∧ (G.rotation e).1 ∈ W

def edgeCount (G : PortGraph V P) (U W : Finset V) : ℕ :=
  (G.edgesBetween U W).card

/-- The only spectral consequence needed by the global distance proof. -/
def HasMixing (G : PortGraph V P) (ε : ℝ) : Prop :=
  ∀ U W : Finset V,
    (G.edgeCount U W : ℝ) ≤
      (Fintype.card P : ℝ) * U.card * W.card / Fintype.card V +
      ε * Fintype.card P * Real.sqrt ((U.card : ℝ) * W.card)

/-- Semantic Tanner constraints before turning the local checks into one
explicit sparse matrix. -/
def IsTannerCodeword {R : Type*} (G : PortGraph V P)
    (Q : CheckMatrix R P) (w : V × P → F3) : Prop :=
  (∀ v, IsCodeword Q (leftWord w v)) ∧
  (∀ v, IsCodeword Q (G.rightWord w v))

end PortGraph

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
