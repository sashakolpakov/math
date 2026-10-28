import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpLeafSemantics

namespace OAI.Algorithms

/-! Exact raw-scope provenance and the paid raw-slot incidence bounds. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

@[simp] theorem rawTerms_member {n m depth : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n))) (h : HashFamily.Candidate m depth)
    (term : Term) :
    term ∈ rawTerms weight source h ↔
      ∃ j, term=(weight (h.2 j),(source (h.1 j)).map Encoding.literalCode) := by
  simp [rawTerms,HashInputProgram.rawRow,List.map_ofFn,eq_comm]

theorem mem_raw_scope {n m depth : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n))) (h : HashFamily.Candidate m depth)
    (v : ℕ) :
    v ∈ scope (rawTerms weight source h) ↔
      ∃ j, ∃ l ∈ source (h.1 j), l.variable.val=v := by
  rw [mem_scope]
  constructor
  · rintro ⟨term,ht,code,hc,he⟩
    obtain ⟨j,rfl⟩ := (rawTerms_member weight source h term).mp ht
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hc
    exact ⟨j,l,hl,(SubexponentialSAT.SubexpLeafSemantics.literalCode_div_two l).symm.trans he⟩
  · rintro ⟨j,l,hl,he⟩
    refine ⟨_,(rawTerms_member weight source h _).mpr ⟨j,rfl⟩,
      Encoding.literalCode l,List.mem_map.mpr ⟨l,hl,rfl⟩,?_⟩
    exact (SubexponentialSAT.SubexpLeafSemantics.literalCode_div_two l).trans he

theorem raw_scope_lt {n m depth : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n))) (h : HashFamily.Candidate m depth) :
    ∀ v ∈ scope (rawTerms weight source h), v < n := by
  intro v hv
  obtain ⟨j,l,hl,he⟩ := (mem_raw_scope weight source h v).mp hv
  exact he ▸ l.variable.isLt

theorem raw_scope_length_le {n m depth k : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n))) (h : HashFamily.Candidate m depth)
    (hw : ∀ i, (source i).length ≤ k) :
    (scope (rawTerms weight source h)).length ≤ depth*k := by
  apply (scope_length_le (rawTerms weight source h)).trans
  simpa [rawTerms,List.map_map,Function.comp_def] using HashInputProgram.rawRow_literal_count source h hw

/-- The reduced ternary row may cancel slots; every remaining algebraic
variable is still included in the larger physically emitted raw scope. -/
theorem hashScope_mem_raw {n m depth : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n))) (h : HashFamily.Candidate m depth)
    (v : Fin n)
    (hv : v ∈ HashInput.hashScope (fun i => (source i).toFinset) (HashFamily.row h)) :
    v.val ∈ scope (rawTerms weight source h) := by
  classical
  obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
  have hn : HashFamily.row h i ≠ 0 := by
    simpa [HashInput.rowSupport] using hi
  unfold HashFamily.row at hn
  obtain ⟨j,_,hj'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hj : h.1 j=i := by
    by_cases he : h.1 j=i
    · exact he
    · simp [he] at hj'
  obtain ⟨l,hl,hv⟩ := Finset.mem_image.mp hv
  apply (mem_raw_scope weight source h v.val).mpr
  refine ⟨j,l,?_,congrArg Fin.val hv⟩
  simpa only [hj,List.mem_toFinset] using hl

/-- Scope mass is charged to raw tuple slots, not surviving nonzero entries. -/
theorem raw_scope_mass_le {n m depth k : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n)))
    (hs : List (HashFamily.Candidate m depth))
    (hw : ∀ i, (source i).length ≤ k) :
    (hs.map fun h => (scope (rawTerms weight source h)).length).sum ≤ hs.length*(depth*k) := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
      have hh := raw_scope_length_le weight source h hw
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
