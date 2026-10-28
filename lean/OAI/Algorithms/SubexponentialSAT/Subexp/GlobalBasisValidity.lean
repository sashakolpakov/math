import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisInput
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisPrepareColumns

namespace OAI.Algorithms

/-!
# Generated global columns satisfy the physical reader bounds

The entry program needs bounds only when a covered row matches the
descriptor's block and color. Actual side-list lengths and local split
bounds imply all of these premises. No matrix values or execution traces
are assumed here.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisValidity

open MulticolorTypes GlobalBasisInput GlobalBasisProgram
open GlobalBasisColumns (Descriptor)

variable {p r Q Δ : ℕ} [Fact p.Prime]
variable (C : Context p r Q Δ)

omit [Fact p.Prime] in
theorem localColumn_valid (loc : Location r Q Δ) (block : ℕ) (g : Fin r)
    (column : ℕ) (hcolumn : column < (C.tables g).dimension) :
    GlobalBasisEntry.Valid (C.row loc) (.localColumn block g.val column) := by
  cases loc with
  | leftover rank =>
    simp [Context.row, GlobalBasisRowPrepare.leftoverRow, GlobalBasisEntry.Valid]
  | covered rowBlock u =>
    change true = true → rowBlock = block → (u.head C.position).val = g.val → _
    intro _ _ hg
    have he : u.head C.position = g := Fin.ext hg
    subst g
    constructor
    · change GlobalBasisCoveredRow.coordinate u C.position < (C.tables (u.head C.position)).dimension
      rw [C.dimensions]
      exact GlobalBasisCoveredRow.coordinate_lt u C.position
    · exact hcolumn

omit [Fact p.Prime] in
theorem leftover_valid (loc : Location r Q Δ) (rank : ℕ) :
    GlobalBasisEntry.Valid (C.row loc) (.leftover rank) := trivial

omit [Fact p.Prime] in
/-- The generated inner descriptors never read beyond their actual local
square table. This discharges the inner phase's entire validity premise. -/
theorem innerDescriptors_valid (loc : Location r Q Δ) (count : ℕ) (g : Fin r)
    (hsplit : (C.tables g).split ≤ (C.tables g).dimension)
    (x : Descriptor) (hx : x ∈ innerDescriptors count g.val (C.tables g).split) :
    GlobalBasisEntry.Valid (C.row loc) x := by
  obtain ⟨block, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨column, hc, rfl⟩ := List.mem_map.mp hx
  exact localColumn_valid C loc block g column ((List.mem_range.mp hc).trans_le hsplit)

private theorem data_at (entry : GlobalBasisComplementColumns.LocalData × ℕ)
    (hentry : entry ∈ C.data.zipIdx) :
    ∃ hg : entry.2 < r, entry.1 = (C.tables ⟨entry.2, hg⟩).data := by
  have hg : entry.2 < r := by
    have h := List.snd_lt_of_mem_zipIdx hentry
    simpa only [Context.data, List.length_ofFn, Nat.add_zero] using h
  refine ⟨hg, ?_⟩
  have hget := List.mem_zipIdx_iff_getElem?.mp hentry
  have hexact : C.data[entry.2]? = some (C.tables ⟨entry.2, hg⟩).data := by
    simp [Context.data, hg]
  exact Option.some.inj (hget.symm.trans hexact)

/-- Complement columns are generated only in the suffix of the local
table, and leftover columns do not access a local table. -/
theorem outerDescriptors_valid (loc : Location r Q Δ) (count leftovers : ℕ)
    (x : Descriptor) (hx : x ∈ outerDescriptors count leftovers C.data) :
    GlobalBasisEntry.Valid (C.row loc) x := by
  rcases List.mem_append.mp hx with hleft | hlocal
  · obtain ⟨rank, _, rfl⟩ := List.mem_map.mp hleft
    exact leftover_valid C loc rank
  · obtain ⟨block, _, hlocal⟩ := List.mem_flatMap.mp hlocal
    obtain ⟨entry, hentry, hlocal⟩ := List.mem_flatMap.mp hlocal
    obtain ⟨column, hc, rfl⟩ := List.mem_map.mp hlocal
    obtain ⟨hg, he⟩ := data_at C entry hentry
    have hcolumn : entry.1.rank + column < (C.tables ⟨entry.2, hg⟩).dimension := by
      have h := List.mem_range.mp hc
      rw [he] at h ⊢
      dsimp [LocalTable.data] at h ⊢
      omega
    exact localColumn_valid C loc block ⟨entry.2, hg⟩ _ hcolumn

end SubexponentialSAT.Subexp.GlobalBasisValidity

end OAI.Algorithms
