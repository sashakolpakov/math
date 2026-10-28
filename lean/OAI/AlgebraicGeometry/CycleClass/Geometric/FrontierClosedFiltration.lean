import Mathlib.Topology.Sets.Closeds
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Fin.Rev

/-! # Frontier Closed Filtration -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FrontierClosedFiltration.Cycles

/-!
# Closed filtrations from finite ordered strata

If the boundary of each member of a finite list lies in the union of later
members, every tail union is closed. Reversing these tails gives an increasing
finite filtration by actual closed subsets. For a pairwise disjoint list,
each difference in the filtration is exactly one of the original subsets.
-/

open _root_.TopologicalSpace

universe u

variable {X : Type u}

/-- The union of a finite ordered list of subsets. -/
def listSupport : List (Set X) → Set X
  | [] => ∅
  | S :: Ss => S ∪ listSupport Ss

@[simp]
theorem listSupport_nil : Cycles.listSupport ([] : List (Set X)) = ∅ := rfl

@[simp]
theorem listSupport_cons (S : Set X) (Ss : List (Set X)) :
    Cycles.listSupport (S :: Ss) = S ∪ Cycles.listSupport Ss := rfl

theorem mem_listSupport {x : X} (Ss : List (Set X)) :
    x ∈ Cycles.listSupport Ss ↔ ∃ S ∈ Ss, x ∈ S := by
  induction Ss with
  | nil => simp [Cycles.listSupport]
  | cons S Ss ih => simp [Cycles.listSupport, ih]

theorem listSupport_eq_iUnion (Ss : List (Set X)) :
    Cycles.listSupport Ss = ⋃ S ∈ Ss, S := by
  ext x
  rw [mem_listSupport]
  constructor
  · rintro ⟨S, hS, hxS⟩
    exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hS, hxS⟩⟩
  · intro hx
    obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hmem, hxS⟩ := Set.mem_iUnion.mp hS
    exact ⟨S, hmem, hxS⟩

theorem listSupport_mono {Ss Ts : List (Set X)} (h : Ss ⊆ Ts) :
    Cycles.listSupport Ss ⊆ Cycles.listSupport Ts := by
  intro x hx
  obtain ⟨S, hS, hxS⟩ := (mem_listSupport Ss).mp hx
  exact (mem_listSupport Ts).mpr ⟨S, h hS, hxS⟩

variable [TopologicalSpace X]

/-- The boundary of every subset is contained in the union of later subsets. -/
def listFrontier : List (Set X) → Prop
  | [] => True
  | S :: Ss => closure S \ S ⊆ Cycles.listSupport Ss ∧ listFrontier Ss

theorem listFrontier_drop (Ss : List (Set X)) (h : Cycles.listFrontier Ss) (n : ℕ) :
    Cycles.listFrontier (Ss.drop n) := by
  induction n generalizing Ss with
  | zero => exact h
  | succ n ih =>
    cases Ss with
    | nil => trivial
    | cons S Ss => exact ih Ss h.2

/-- A finite union with this ordered frontier condition is closed. -/
theorem listSupport_isClosed (Ss : List (Set X)) (h : Cycles.listFrontier Ss) :
    IsClosed (Cycles.listSupport Ss) := by
  classical
  induction Ss with
  | nil => exact isClosed_empty
  | cons S Ss ih =>
    change IsClosed (S ∪ Cycles.listSupport Ss)
    apply closure_eq_iff_isClosed.mp
    apply Set.Subset.antisymm _ subset_closure
    rw [closure_union, (ih h.2).closure_eq]
    intro x hx
    rcases hx with hx | hx
    · by_cases hxS : x ∈ S
      · exact Or.inl hxS
      · exact Or.inr (h.1 ⟨hx, hxS⟩)
    · exact Or.inr hx

/-- Every tail of an ordered frontier list has a closed union. -/
theorem listSupport_drop_isClosed (Ss : List (Set X)) (h : Cycles.listFrontier Ss) (n : ℕ) :
    IsClosed (Cycles.listSupport (Ss.drop n)) :=
  listSupport_isClosed (Ss.drop n) (listFrontier_drop Ss h n)

omit [TopologicalSpace X] in
theorem listSupport_drop_antitone (Ss : List (Set X)) :
    Antitone (fun n => Cycles.listSupport (Ss.drop n)) := by
  intro i j hij
  exact listSupport_mono (List.drop_subset_drop_left Ss hij)

omit [TopologicalSpace X] in
theorem disjoint_listSupport (S : Set X) (Ss : List (Set X))
    (h : ∀ T ∈ Ss, Disjoint S T) : Disjoint S (Cycles.listSupport Ss) := by
  apply Set.disjoint_left.mpr
  intro x hxS hx
  obtain ⟨T, hT, hxT⟩ := (mem_listSupport Ss).mp hx
  exact Set.disjoint_left.mp (h T hT) hxS hxT

omit [TopologicalSpace X] in
/-- Removing the next tail from a tail leaves exactly its first stratum. -/
theorem listSupport_drop_layer (Ss : List (Set X)) (h : Ss.Pairwise Disjoint)
    (i : Fin Ss.length) :
    Cycles.listSupport (Ss.drop i.val) \ Cycles.listSupport (Ss.drop (i.val + 1)) = Ss.get i := by
  have htail : (Ss.get i :: Ss.drop (i.val + 1)).Pairwise Disjoint := by
    rw [List.cons_get_drop_succ]
    exact h.drop
  have hd := disjoint_listSupport (Ss.get i) (Ss.drop (i.val + 1))
    (List.pairwise_cons.mp htail).1
  rw [← List.cons_get_drop_succ (n := i), listSupport_cons]
  ext x
  constructor
  · rintro ⟨hx, hxnot⟩
    exact hx.resolve_right hxnot
  · intro hx
    exact ⟨Or.inl hx, fun hxt => Set.disjoint_left.mp hd hx hxt⟩

/-- Reversed tail unions form a finite family of actual closed subsets. -/
def frontierClosedFiltration (Ss : List (Set X)) (h : Cycles.listFrontier Ss) :
    Fin (Ss.length + 1) → Closeds X :=
  fun i => ⟨Cycles.listSupport (Ss.drop i.rev.val), listSupport_drop_isClosed Ss h i.rev.val⟩

@[simp]
theorem frontierClosedFiltration_coe (Ss : List (Set X)) (h : Cycles.listFrontier Ss)
    (i : Fin (Ss.length + 1)) :
    (frontierClosedFiltration Ss h i : Set X) = Cycles.listSupport (Ss.drop i.rev.val) := rfl

theorem frontierClosedFiltration_monotone (Ss : List (Set X)) (h : Cycles.listFrontier Ss) :
    Monotone (frontierClosedFiltration Ss h) := by
  intro i j hij
  exact listSupport_drop_antitone Ss (show j.rev.val ≤ i.rev.val from Fin.rev_le_rev.mpr hij)

@[simp]
theorem frontierClosedFiltration_zero (Ss : List (Set X)) (h : Cycles.listFrontier Ss) :
    frontierClosedFiltration Ss h 0 = ⊥ := by
  apply Closeds.ext
  simp [frontierClosedFiltration]

@[simp]
theorem frontierClosedFiltration_last (Ss : List (Set X)) (h : Cycles.listFrontier Ss) :
    (frontierClosedFiltration Ss h (Fin.last Ss.length) : Set X) = Cycles.listSupport Ss := by
  simp [frontierClosedFiltration]

/-- Each layer is the original stratum with the reversed finite index. -/
theorem frontierClosedFiltration_layer (Ss : List (Set X)) (hf : Cycles.listFrontier Ss)
    (hd : Ss.Pairwise Disjoint) (i : Fin Ss.length) :
    (frontierClosedFiltration Ss hf i.succ : Set X) \
        (frontierClosedFiltration Ss hf i.castSucc : Set X) = Ss.get i.rev := by
  change Cycles.listSupport (Ss.drop i.succ.rev.val) \ Cycles.listSupport (Ss.drop i.castSucc.rev.val) = _
  simpa only [Fin.rev_succ, Fin.rev_castSucc, Fin.val_castSucc, Fin.val_succ] using
    listSupport_drop_layer Ss hd i.rev

/-- The same layer identity indexed directly by the original stratum. -/
theorem frontierClosedFiltration_layer_rev (Ss : List (Set X)) (hf : Cycles.listFrontier Ss)
    (hd : Ss.Pairwise Disjoint) (i : Fin Ss.length) :
    (frontierClosedFiltration Ss hf i.rev.succ : Set X) \
        (frontierClosedFiltration Ss hf i.rev.castSucc : Set X) = Ss.get i := by
  simpa only [Fin.rev_rev] using frontierClosedFiltration_layer Ss hf hd i.rev

end OAI.AlgebraicGeometry.CycleClass.Geometric.FrontierClosedFiltration.Cycles
