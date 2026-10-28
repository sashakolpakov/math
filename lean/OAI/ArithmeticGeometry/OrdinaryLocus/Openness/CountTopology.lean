import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Semicontinuity.Basic

/-! # Count Topology -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CountTopology.Construction

/-! The topological maximal-count argument used in the torsion approach to Openness. -/

variable {X : Type*} [TopologicalSpace X]

/-- A count attains a locally constant upper bound on an open set when
all its lower-threshold loci are open. -/
theorem isOpen_maximalCount
    (count bound : X → ℕ)
    (hcount : ∀ n : ℕ, IsOpen {x : X | n ≤ count x})
    (hbound : IsLocallyConstant bound)
    (hle : ∀ x, count x ≤ bound x) :
    IsOpen {x : X | count x = bound x} := by
  have heq : {x : X | count x = bound x} =
      ⋃ n : ℕ, {x : X | bound x = n} ∩ {x : X | n ≤ count x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      exact ⟨bound x, rfl, hx.ge⟩
    · rintro ⟨n, hn, hnx⟩
      exact le_antisymm (hle x) (hn ▸ hnx)
  rw [heq]
  exact isOpen_iUnion fun n => (hbound.isOpen_fiber n).inter (hcount n)

/-- The threshold hypothesis follows from ordinary lower semicontinuity
for a natural-valued function, including its zero threshold. -/
theorem isOpen_nat_ge_of_lowerSemicontinuous
    (count : X → ℕ) (hc : LowerSemicontinuous count) (n : ℕ) :
    IsOpen {x : X | n ≤ count x} := by
  cases n with
  | zero => simp
  | succ n =>
    simpa only [Nat.succ_le_iff, Set.preimage_ofPred_eq, Set.Ioi] using hc.isOpen_preimage n

theorem isOpen_maximalCount_of_lowerSemicontinuous
    (count bound : X → ℕ)
    (hcount : LowerSemicontinuous count)
    (hbound : IsLocallyConstant bound)
    (hle : ∀ x, count x ≤ bound x) :
    IsOpen {x : X | count x = bound x} :=
  isOpen_maximalCount count bound
    (isOpen_nat_ge_of_lowerSemicontinuous count hcount) hbound hle

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CountTopology.Construction
