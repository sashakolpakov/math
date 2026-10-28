import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasis
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntry

namespace OAI.Algorithms

/-!
# Physical descriptors denote the explicit global columns

The matrix-entry callback uses full local column numbers. In particular a
complement index j denotes column d+j in the searched square table. These
lemmas identify that callback with the global synthesis matrices, in the
actual side and packing order.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisDescriptors

open BlockSearch BlockSearchEncoding GlobalBasis GlobalBasisEntry
open GlobalBasisColumns (Descriptor)
open LocalEnumeration ComputablePackingSplit

variable {p r b l : ℕ} [Fact p.Prime]
variable {U V : Type*} [Fintype U] [DecidableEq V]
variable {n m : Fin r → ℕ}
variable (color : U → Fin r) (sideIndex : ∀ g, Fin (n g) ≃ ColorFiber color g)
variable (constraint : ∀ g, Fin (m g) → Fin (n g) → ZMod p)
variable (pairs : ∀ g, Candidate (ZMod p) (n g) × Candidate (ZMod p) (n g))
variable (good : ∀ g, GoodPair (constraint g) (pairs g))
variable (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
variable (packing : Fin b × U ↪ V) (leftovers : Fin l ≃ Leftover packing)

def outerDescriptor : OuterColumn (b := b) (l := l) pairs → Descriptor
  | .inl j => .leftover j.val
  | .inr (block, ⟨g, j⟩) => .localColumn block.val g.val ((pairs g).1.1.val + j.val)

def innerDescriptor (g : Fin r) (c : InnerColumn (b := b) pairs g) : Descriptor :=
  .localColumn c.1.val g.val c.2.val

def columnDescriptor : Column (b := b) (l := l) pairs → Descriptor
  | .inl c => outerDescriptor pairs c
  | .inr ⟨g, c⟩ => innerDescriptor pairs g c

/-- Metadata and local table for an actually covered ambient coordinate. -/
def coveredRow (block : Fin b) (u : U) : Row p where
  N := n (color u)
  table := tableOfPair (pairs (color u)) (BlockSearchEncoding.dimensions_add (good (color u)))
  coordinate := ((sideIndex (color u)).symm ⟨u, rfl⟩).val
  block := block.val
  color := (color u).val
  rank := 0
  covered := true

/-- A leftover row needs only its actual rank; no local table is read. -/
def leftoverRow (j : Fin l) : Row p where
  N := 0
  table i := nomatch i
  coordinate := 0
  block := 0
  color := 0
  rank := j.val
  covered := false

omit [Fintype U] in
/-- Every emitted column is a legal input to the physical cell reader.
Its range checks follow from the successful local pair, rather than an
additional runtime-correctness premise. -/
theorem coveredRow_valid (block : Fin b) (u : U)
    (c : Column (b := b) (l := l) pairs) :
    Valid (coveredRow color sideIndex constraint pairs good block u)
      (columnDescriptor pairs c) := by
  cases c with
  | inl c =>
    cases c with
    | inl j => trivial
    | inr c =>
      rcases c with ⟨block', g, j⟩
      change true = true → block.val = block'.val → (color u).val = g.val → _
      intro _ _ hg
      have he : color u = g := Fin.ext hg
      subst g
      constructor
      · exact ((sideIndex (color u)).symm ⟨u, rfl⟩).isLt
      · have hd := BlockSearchEncoding.dimensions_add (good (color u))
        have := j.isLt
        change (pairs (color u)).1.1.val + j.val < n (color u)
        omega
  | inr c =>
    rcases c with ⟨g, block', j⟩
    change true = true → block.val = block'.val → (color u).val = g.val → _
    intro _ _ hg
    have he : color u = g := Fin.ext hg
    subst g
    constructor
    · exact ((sideIndex (color u)).symm ⟨u, rfl⟩).isLt
    · have hd := BlockSearchEncoding.dimensions_add (good (color u))
      have := j.isLt
      change j.val < n (color u)
      omega

omit [Fact p.Prime] in
theorem leftoverRow_valid (j : Fin l) (c : Column (b := b) (l := l) pairs) :
    Valid (leftoverRow (p := p) j) (columnDescriptor pairs c) := by
  cases c with
  | inl c =>
    cases c with
    | inl _ => trivial
    | inr c => simp [Valid, columnDescriptor, outerDescriptor, leftoverRow]
  | inr c =>
    rcases c with ⟨g, c⟩
    simp [Valid, columnDescriptor, innerDescriptor, leftoverRow]

theorem coveredRow_kernel (block block' : Fin b) (u : U) (g : Fin r)
    (j : KernelIndex pairs g) :
    value (coveredRow color sideIndex constraint pairs good block u)
      (innerDescriptor pairs g (block', j)) =
      matrix color sideIndex constraint pairs good alphabet complete packing leftovers
        (packing (block, u)) (.inr ⟨g, (block', j)⟩) := by
  rw [matrix_kernel_column]
  by_cases hg : color u = g
  · subst g
    by_cases hb : block = block'
    · subst block'
      have hj : j.val < n (color u) := by
        have hd := BlockSearchEncoding.dimensions_add (good (color u))
        have := j.isLt
        omega
      simp [value, innerDescriptor, localValue, blockValue, colorValue,
        coveredRow, Row.cell, hj, tableOfPair_first]
    · simp [value, innerDescriptor, localValue, blockValue,
        coveredRow, Fin.val_inj, hb]
  · simp [value, innerDescriptor, localValue, blockValue, colorValue,
      coveredRow, Fin.val_inj, hg]

theorem coveredRow_complement (block block' : Fin b) (u : U) (g : Fin r)
    (j : ComplementIndex pairs g) :
    value (coveredRow color sideIndex constraint pairs good block u)
      (outerDescriptor (l := l) pairs (.inr (block', ⟨g, j⟩))) =
      matrix color sideIndex constraint pairs good alphabet complete packing leftovers
        (packing (block, u)) (.inl (.inr (block', ⟨g, j⟩))) := by
  rw [matrix_complement_column]
  by_cases hg : color u = g
  · subst g
    by_cases hb : block = block'
    · subst block'
      have hj : (pairs (color u)).1.1.val + j.val < n (color u) := by
        have hd := BlockSearchEncoding.dimensions_add (good (color u))
        have := j.isLt
        omega
      simp [value, outerDescriptor, localValue, blockValue, colorValue,
        coveredRow, Row.cell, hj, tableOfPair_second]
    · simp [value, outerDescriptor, localValue, blockValue,
        coveredRow, Fin.val_inj, hb]
  · simp [value, outerDescriptor, localValue, blockValue, colorValue,
      coveredRow, Fin.val_inj, hg]

theorem coveredRow_value (block : Fin b) (u : U)
    (c : Column (b := b) (l := l) pairs) :
    value (coveredRow color sideIndex constraint pairs good block u)
      (columnDescriptor pairs c) =
      matrix color sideIndex constraint pairs good alphabet complete packing leftovers
        (packing (block, u)) c := by
  cases c with
  | inl c =>
    cases c with
    | inl j =>
      rw [matrix_leftover_column]
      rfl
    | inr c =>
      rcases c with ⟨block', g, j⟩
      exact coveredRow_complement color sideIndex constraint pairs good alphabet complete
        packing leftovers block block' u g j
  | inr c =>
    rcases c with ⟨g, block', j⟩
    exact coveredRow_kernel color sideIndex constraint pairs good alphabet complete
      packing leftovers block block' u g j

theorem leftoverRow_value (j : Fin l) (c : Column (b := b) (l := l) pairs) :
    value (leftoverRow (p := p) j) (columnDescriptor pairs c) =
      matrix color sideIndex constraint pairs good alphabet complete packing leftovers
        (leftovers j).val c := by
  rw [matrix_leftover]
  simp only [Equiv.symm_apply_apply]
  cases c with
  | inl c =>
    cases c with
    | inl j' =>
      simp [columnDescriptor, outerDescriptor, value, leftoverValue, leftoverRow,
        Fin.val_inj, eq_comm]
    | inr c =>
      simp [columnDescriptor, outerDescriptor, value, localValue, leftoverRow]
  | inr c =>
    rcases c with ⟨g, block', j'⟩
    simp [columnDescriptor, innerDescriptor, value, localValue, leftoverRow]

theorem coveredRow_outerMatrix (block : Fin b) (u : U)
    (j : Fin (outerList (b := b) (l := l) pairs).length) :
    value (coveredRow color sideIndex constraint pairs good block u)
      (outerDescriptor pairs ((outerEnumeration (b := b) (l := l) pairs).equivFin j)) =
      outerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers
        (packing (block, u)) j :=
  coveredRow_value color sideIndex constraint pairs good alphabet complete packing leftovers
    block u (.inl ((outerEnumeration (b := b) (l := l) pairs).equivFin j))

theorem coveredRow_innerMatrix (block : Fin b) (u : U) (g : Fin r)
    (j : Fin (innerList (b := b) pairs g).length) :
    value (coveredRow color sideIndex constraint pairs good block u)
      (innerDescriptor pairs g ((innerEnumeration (b := b) pairs g).equivFin j)) =
      innerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers g
        (packing (block, u)) j :=
  coveredRow_value color sideIndex constraint pairs good alphabet complete packing leftovers
    block u (.inr ⟨g, (innerEnumeration (b := b) pairs g).equivFin j⟩)

end SubexponentialSAT.Subexp.GlobalBasisDescriptors

end OAI.Algorithms
