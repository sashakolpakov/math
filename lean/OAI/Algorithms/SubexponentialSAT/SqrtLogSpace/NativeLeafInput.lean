import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

/-! Physical leaf input facts after the actual terminal dispatcher. The
number of clauses is bounded using the disjoint selector's occurrence
estimate; no OR-cover leaf multiplicity is used. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafInput

open DisjointReuse DisjointReuse.SparseDFSRefinement DisjointReuse.DFSVisit

variable {n k parameterBound : ℕ}

/-- Valid raw syntax has one record per semantic clause. -/
theorem length_eq_card (F : RawCNF n) (hv : Valid k F) :
    F.length = (ExecCNF.formulaSet F).card := by
  simpa only [ExecCNF.formulaSet, List.length_map] using
    (List.toFinset_card_of_nodup hv.clause_nodup).symm

/-- The terminal empty-clause test agrees with the semantic set input. -/
theorem empty_not_mem (F : RawCNF n) (h : [] ∉ F) :
    (∅ : SAT.Clause (Fin n)) ∉ ExecCNF.formulaSet F := by
  intro hm
  obtain ⟨C, hC, he⟩ := ExecCNF.mem_formulaSet.mp hm
  have hz : C = [] := List.toFinset_eq_empty_iff C |>.mp he
  exact h (hz ▸ hC)

/-- Incidence counting for nonempty clauses. This is the source's elementary
clause bound, independent of the overlapping sparsification controller. -/
theorem card_le_occurrences (G : SAT.CNF (Fin n)) (B : ℕ)
    (hB : ∀ v, SAT.occurrences v G ≤ B)
    (hempty : (∅ : SAT.Clause (Fin n)) ∉ G) : G.card ≤ n * B := by
  let occ := fun v : Fin n => G.filter (fun C => ∃ l ∈ C, l.variable = v)
  have hcover : G ⊆ Finset.univ.biUnion occ := by
    intro C hC
    have hne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro he
      exact hempty (he ▸ hC))
    obtain ⟨l, hl⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨l.variable, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hC, l, hl, rfl⟩⟩
  calc
    G.card ≤ (Finset.univ.biUnion occ).card := Finset.card_le_card hcover
    _ ≤ ∑ v : Fin n, (occ v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n, B := Finset.sum_le_sum (fun v _ => hB v)
    _ = n * B := by simp

/-- The occurrence word on physical stack264 bounds the actual record count.
Both the selector and the input remain over the declared ambient Fin n. -/
theorem clauses_le_physical_occurrence (F : RawCNF n)
    (threshold : List Bool) (a : StructuredProgram.State 80 1220)
    (hk : 0 < k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hv : Valid k F) (hr : LeafReady k threshold parameterBound F a)
    (hs : SparsePriority.select (ExecCNF.formulaSet F)
      (BinaryArithmetic.toNat threshold) = none) (hempty : [] ∉ F) :
    F.length ≤ n * BinaryArithmetic.toNat (a.stacks 264) := by
  have ho := SparseBudget.leaf_occurrences_le_power (ExecCNF.formulaSet F) k
    (BinaryArithmetic.toNat threshold) hk hM (formulaSet_width_le F hv.width) hs
  rw [length_eq_card F hv, hr.dimension]
  exact card_le_occurrences _ _ ho (empty_not_mem F hempty)

/-- The exact serialized records consumed by startup retain the physical
body and the actual number of clauses. -/
theorem records_input (F : RawCNF n) (threshold : List Bool)
    (a : StructuredProgram.State 80 1220) (hr : LeafReady k threshold parameterBound F a)
    (hne : F ≠ []) :
    a.stacks 265 = Encoding.encodeList id (NativeTerminal.clauseRecords F) ∧
      (NativeTerminal.clauseRecords F).length = F.length ∧
      NativeTerminal.clauseRecords F ≠ [] := by
  refine ⟨?_, by simp [NativeTerminal.clauseRecords], ?_⟩
  · exact hr.current.trans (NativeTerminal.clauseRecords_body F).symm
  · exact fun h => hne ((NativeTerminal.clauseRecords_nil_iff F).mp h)

/-- Nonterminal startup has a positive clause count and a positive supplied
occurrence bound; the latter is an actual decoded word, possibly padded. -/
theorem nonterminal_positive (F : RawCNF n) (threshold : List Bool)
    (a : StructuredProgram.State 80 1220) (hr : LeafReady k threshold parameterBound F a)
    (hM : 2 ≤ BinaryArithmetic.toNat threshold) (hne : F ≠ []) :
    0 < (NativeTerminal.clauseRecords F).length ∧
      0 < BinaryArithmetic.toNat (a.stacks 264) := by
  constructor
  · simpa only [NativeTerminal.clauseRecords, List.length_map] using List.length_pos_iff.mpr hne
  · rw [hr.dimension]
    exact Nat.mul_pos (by decide) (Nat.pow_pos (by omega))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafInput
