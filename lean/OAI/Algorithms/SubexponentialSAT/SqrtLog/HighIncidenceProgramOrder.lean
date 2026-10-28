import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramRestriction
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramRank

namespace OAI.Algorithms

/-! The physical mask traverses original coordinates in descending order.
This explicit order, rather than an arbitrary finite-type equivalence,
identifies each odometer position with its actual original variable. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

def coordinates (n : ℕ) : List (Fin n) := (List.finRange n).reverse

def highCoordinates {n : ℕ} (H : Finset (Fin n)) : List (Fin n) :=
  (coordinates n).filter (fun v => decide (v ∈ H))

theorem highCoordinates_nodup {n : ℕ} (H : Finset (Fin n)) :
    (highCoordinates H).Nodup := by
  exact (List.nodup_reverse.mpr (List.nodup_finRange n)).filter _

@[simp] theorem mem_highCoordinates {n : ℕ} (H : Finset (Fin n)) (v : Fin n) :
    v ∈ highCoordinates H ↔ v ∈ H := by
  simp [highCoordinates, coordinates]

def rawOrder {n : ℕ} (H : Finset (Fin n)) : Fin (highCoordinates H).length ≃ H :=
  (List.Nodup.getEquiv (highCoordinates H) (highCoordinates_nodup H)).trans
    (Equiv.subtypeEquivRight (mem_highCoordinates H))

@[simp] theorem highCoordinates_length {n : ℕ} (H : Finset (Fin n)) :
    (highCoordinates H).length = H.card := by
  simpa using Fintype.card_congr (rawOrder H)

def highOrder {n : ℕ} (H : Finset (Fin n)) : Fin H.card ≃ H :=
  (finCongr (highCoordinates_length H).symm).trans (rawOrder H)

theorem highOrder_val {n : ℕ} (H : Finset (Fin n)) (i : Fin H.card) :
    (highOrder H i).val = (highCoordinates H).get
      ⟨i.val, by simp⟩ := by
  rfl

theorem highOrder_stream {n : ℕ} (H : Finset (Fin n)) (x : Fin n → Bool) :
    List.ofFn (fun i : Fin H.card => x (highOrder H i)) = (highCoordinates H).map x := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp only [ highOrder_val, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]

theorem selected_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    Restriction.selected true (xs.map p) (xs.map x) = (xs.filter p).map x := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [Restriction.selected, hp, ih]

theorem highPrefix_range (scopes : List (List ℕ)) (cut n : ℕ) :
    highPrefix scopes cut n = (List.range n).reverse.map (fun v => decide (cut < degree scopes v)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [highPrefix, List.range_succ, ih]

theorem physical_mask (scopes : List (List ℕ)) (cut n : ℕ) :
    highPrefix scopes cut n = (coordinates n).map
      (fun v => decide (v ∈ HighIncidence.high (suppliedScope n scopes) cut)) := by
  rw [highPrefix_range]
  simp only [HighIncidence.high, Finset.mem_filter, Finset.mem_univ, true_and,
    degree_suppliedScope, coordinates]
  rw [← List.map_coe_finRange n, ← List.map_reverse, List.map_map]
  rfl

theorem coordinates_stream (n : ℕ) (x : Fin n → Bool) :
    (coordinates n).map x = (List.ofFn x).reverse := by
  simp only [coordinates, List.map_reverse, List.ofFn_eq_map]

/-- The selected high bits consumed by the physical merger are exactly the
odometer bits indexed by highOrder. -/
theorem selected_high_stream (scopes : List (List ℕ)) (cut n : ℕ) (x : Fin n → Bool) :
    Restriction.selected true (highPrefix scopes cut n) ((List.ofFn x).reverse) =
      List.ofFn (fun i : Fin (HighIncidence.high (suppliedScope n scopes) cut).card =>
        x (highOrder (HighIncidence.high (suppliedScope n scopes) cut) i)) := by
  rw [physical_mask, ← coordinates_stream, selected_map]
  exact (highOrder_stream _ x).symm

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

end OAI.Algorithms
