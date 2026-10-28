import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNF
import OAI.Algorithms.SubexponentialSAT.ExecSelectedFamilyProgram

namespace OAI.Algorithms

/-!
# Increasing source indices for a selected clause family

The witness scans the source list in order.  It retains exactly the positions
whose records satisfy a decidable predicate.  This is a semantic completeness
lemma for the existing indexed gather program, not an additional machine
instruction or a runtime oracle.
-/

namespace SubexponentialSAT.ExecSelectedFamilyCompleteness

universe u

def gather {β : Type u} (records : List β) (indices : List ℕ) : List β :=
  indices.filterMap (fun i => records[i]?)

def selectIndices {β : Type u} (p : β → Bool) : List β → List ℕ
  | [] => []
  | item :: rest =>
      if p item then 0 :: (selectIndices p rest).map Nat.succ
      else (selectIndices p rest).map Nat.succ

@[simp] theorem gather_nil {β : Type u} (records : List β) :
    gather records [] = [] := rfl

@[simp] theorem gather_zero_cons {β : Type u} (item : β) (records : List β)
    (indices : List ℕ) :
    gather (item :: records) (0 :: indices) = item :: gather (item :: records) indices := rfl

@[simp] theorem gather_succ_map {β : Type u} (item : β) (records : List β)
    (indices : List ℕ) :
    gather (item :: records) (indices.map Nat.succ) = gather records indices := by
  simp only [gather, List.filterMap_map, Function.comp_def, Nat.succ_eq_add_one,
    List.getElem?_cons_succ]

theorem gather_selectIndices {β : Type u} (p : β → Bool) (records : List β) :
    gather records (selectIndices p records) = records.filter p := by
  induction records with
  | nil => rfl
  | cons item rest ih => cases hp : p item <;> simp [selectIndices, hp, ih]

theorem selectIndices_length {β : Type u} (p : β → Bool) (records : List β) :
    (selectIndices p records).length = (records.filter p).length := by
  induction records with
  | nil => rfl
  | cons item rest ih => cases hp : p item <;> simp [selectIndices, hp, ih]

theorem selectIndices_lt_length {β : Type u} (p : β → Bool) (records : List β) :
    ∀ i ∈ selectIndices p records, i < records.length := by
  induction records with
  | nil => simp [selectIndices]
  | cons item rest ih =>
      intro i hi
      cases hp : p item
      · simp only [selectIndices, hp, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        simpa using Nat.succ_lt_succ (ih j hj)
      · simp only [selectIndices, hp, ↓reduceIte, List.mem_cons, List.mem_map] at hi
        rcases hi with rfl | ⟨j, hj, rfl⟩
        · simp
        · simpa using Nat.succ_lt_succ (ih j hj)

theorem selectIndices_increasing {β : Type u} (p : β → Bool) (records : List β) :
    (selectIndices p records).Pairwise (· < ·) := by
  induction records with
  | nil => simp [selectIndices]
  | cons item rest ih =>
      have hm : ((selectIndices p rest).map Nat.succ).Pairwise (· < ·) :=
        ih.map Nat.succ (fun _ _ h => Nat.succ_lt_succ h)
      cases hp : p item
      · simpa [selectIndices, hp] using hm
      · simp only [selectIndices, hp, ↓reduceIte, List.pairwise_cons]
        refine ⟨?_, hm⟩
        intro i hi
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
        exact Nat.succ_pos j

theorem gather_selectIndices_length {β : Type u} (p : β → Bool) (records : List β) :
    (gather records (selectIndices p records)).length = (selectIndices p records).length := by
  rw [gather_selectIndices, selectIndices_length]

theorem gather_subset {β : Type u} (records : List β) (indices : List ℕ) :
    gather records indices ⊆ records := by
  intro item hi
  obtain ⟨i, _, hget⟩ := List.mem_filterMap.mp hi
  exact List.mem_of_getElem? hget

theorem gather_map {β γ : Type u} (f : β → γ) (records : List β) (indices : List ℕ) :
    (gather records indices).map f = gather (records.map f) indices := by
  simp only [gather, List.map_filterMap, List.getElem?_map ]

theorem gather_nodup {β : Type u} (records : List β) (indices : List ℕ)
    (hr : records.Nodup) (hi : indices.Nodup) : (gather records indices).Nodup := by
  apply List.Nodup.filterMap ?_ hi
  intro i j item hgeti hgetj
  obtain ⟨hi, hei⟩ := List.getElem?_eq_some_iff.mp hgeti
  obtain ⟨hj, hej⟩ := List.getElem?_eq_some_iff.mp hgetj
  exact hr.getElem_inj_iff.mp (hei.trans hej.symm)

theorem gather_length_of_valid {β : Type u} (records : List β) (indices : List ℕ)
    (hvalid : ∀ i ∈ indices, i < records.length) :
    (gather records indices).length = indices.length := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      have hi := hvalid i (by simp)
      have ht := ih (fun j hj => hvalid j (by simp [hj]))
      have hg : records[i]? = some records[i] := by simp [hi]
      simpa [gather, hg] using congrArg Nat.succ ht

section Clauses

variable {α : Type u} [DecidableEq α]

def familyIndices (F : ExecCNF.Formula α) (S : Finset (Finset α)) : List ℕ :=
  selectIndices (fun C => decide (ExecCNF.clauseSet C ∈ S)) F

theorem formulaSet_filter_family (F : ExecCNF.Formula α) (S : Finset (Finset α))
    (hS : S ⊆ ExecCNF.formulaSet F) :
    ExecCNF.formulaSet (F.filter (fun C => decide (ExecCNF.clauseSet C ∈ S))) = S := by
  ext C
  constructor
  · intro h
    obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp h
    simpa using (List.mem_filter.mp hD).2
  · intro h
    obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp (hS h)
    exact ExecCNF.mem_formulaSet.mpr
      ⟨D, List.mem_filter.mpr ⟨hD, by simpa using h⟩, rfl⟩

theorem formulaSet_reverse (F : ExecCNF.Formula α) :
    ExecCNF.formulaSet F.reverse = ExecCNF.formulaSet F := by
  simp [ExecCNF.formulaSet, List.map_reverse, List.toFinset_reverse]

theorem familyIndices_increasing (F : ExecCNF.Formula α) (S : Finset (Finset α)) :
    (familyIndices F S).Pairwise (· < ·) :=
  selectIndices_increasing _ _

theorem familyIndices_lt_length (F : ExecCNF.Formula α) (S : Finset (Finset α)) :
    ∀ i ∈ familyIndices F S, i < F.length :=
  selectIndices_lt_length _ _

theorem gather_familyIndices (F : ExecCNF.Formula α) (S : Finset (Finset α)) :
    gather F (familyIndices F S) =
      F.filter (fun C => decide (ExecCNF.clauseSet C ∈ S)) :=
  gather_selectIndices _ _

theorem gather_familyIndices_formulaSet (F : ExecCNF.Formula α)
    (S : Finset (Finset α)) (hS : S ⊆ ExecCNF.formulaSet F) :
    ExecCNF.formulaSet (gather F (familyIndices F S)).reverse = S := by
  rw [formulaSet_reverse, gather_familyIndices, formulaSet_filter_family F S hS]

theorem gather_familyIndices_nodup (F : ExecCNF.Formula α)
    (S : Finset (Finset α)) (hF : (F.map ExecCNF.clauseSet).Nodup) :
    ((gather F (familyIndices F S)).reverse.map ExecCNF.clauseSet).Nodup := by
  rw [List.map_reverse, List.nodup_reverse, gather_familyIndices]
  exact (List.Sublist.map ExecCNF.clauseSet List.filter_sublist).nodup hF

theorem familyIndices_length (F : ExecCNF.Formula α) (S : Finset (Finset α))
    (hF : (F.map ExecCNF.clauseSet).Nodup) (hS : S ⊆ ExecCNF.formulaSet F) :
    (familyIndices F S).length = S.card := by
  have hn : ((F.filter (fun C => decide (ExecCNF.clauseSet C ∈ S))).map
      ExecCNF.clauseSet).Nodup :=
    (List.Sublist.map ExecCNF.clauseSet List.filter_sublist).nodup hF
  have hc := List.toFinset_card_of_nodup hn
  change (ExecCNF.formulaSet (F.filter
    (fun C => decide (ExecCNF.clauseSet C ∈ S)))).card = _ at hc
  rw [formulaSet_filter_family F S hS, List.length_map] at hc
  exact (selectIndices_length _ _).trans hc.symm

/-- Every selected set has an increasing, in-range index witness of exactly its cardinality. -/
theorem exists_indices (F : ExecCNF.Formula α) (S : Finset (Finset α))
    (hF : (F.map ExecCNF.clauseSet).Nodup) (hS : S ⊆ ExecCNF.formulaSet F) :
    ∃ indices : List ℕ,
      indices.Pairwise (· < ·) ∧
      (∀ i ∈ indices, i < F.length) ∧
      indices.length = S.card ∧
      (gather F indices).length = indices.length ∧
      ExecCNF.formulaSet (gather F indices).reverse = S ∧
      ((gather F indices).reverse.map ExecCNF.clauseSet).Nodup :=
  ⟨familyIndices F S, familyIndices_increasing F S, familyIndices_lt_length F S,
    familyIndices_length F S hF hS, gather_selectIndices_length _ _,
    gather_familyIndices_formulaSet F S hS, gather_familyIndices_nodup F S hF⟩

end Clauses

/-- The value-level gather is exactly the existing machine's selected-clause list. -/
theorem selectedClauses_eq_gather (F : List (List (List Bool)))
    (words : List (List Bool)) :
    ExecSelectedFamilyProgram.selectedClauses F words =
      gather F (words.map CounterPrograms.value) := by
  simp only [ExecSelectedFamilyProgram.selectedClauses, gather,
    List.filterMap_map, Function.comp_def]

theorem selectedClauses_subset (F : List (List (List Bool)))
    (words : List (List Bool)) :
    ExecSelectedFamilyProgram.selectedClauses F words ⊆ F := by
  rw [selectedClauses_eq_gather]
  exact gather_subset _ _

theorem selectedClauses_map_nodup (F : List (List (List Bool)))
    (words : List (List Bool)) (hF : (F.map ExecCNF.clauseSet).Nodup)
    (hindices : (words.map CounterPrograms.value).Nodup) :
    ((ExecSelectedFamilyProgram.selectedClauses F words).reverse.map
      ExecCNF.clauseSet).Nodup := by
  rw [List.map_reverse, List.nodup_reverse, selectedClauses_eq_gather, gather_map]
  exact gather_nodup _ _ hF hindices

theorem selectedClauses_length_of_valid (F : List (List (List Bool)))
    (words : List (List Bool))
    (hvalid : ∀ word ∈ words, CounterPrograms.value word < F.length) :
    (ExecSelectedFamilyProgram.selectedClauses F words).length = words.length := by
  rw [selectedClauses_eq_gather, gather_length_of_valid, List.length_map]
  intro i hi
  obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hi
  exact hvalid word hw

/-- Arbitrary accepted increasing tuples retain source clauses without duplicate clause sets. -/
theorem selectedClauses_sound (F : List (List (List Bool)))
    (words : List (List Bool)) (hF : (F.map ExecCNF.clauseSet).Nodup)
    (hindices : (words.map CounterPrograms.value).Pairwise (· < ·))
    (hvalid : ∀ word ∈ words, CounterPrograms.value word < F.length) :
    (ExecSelectedFamilyProgram.selectedClauses F words).reverse ⊆ F ∧
      ((ExecSelectedFamilyProgram.selectedClauses F words).reverse.map
        ExecCNF.clauseSet).Nodup ∧
      (ExecSelectedFamilyProgram.selectedClauses F words).reverse.length = words.length ∧
      ExecCNF.formulaSet (ExecSelectedFamilyProgram.selectedClauses F words).reverse ⊆
        ExecCNF.formulaSet F := by
  have hsub : (ExecSelectedFamilyProgram.selectedClauses F words).reverse ⊆ F := by
    intro C hC
    exact selectedClauses_subset F words (by simpa using hC)
  refine ⟨hsub, selectedClauses_map_nodup F words hF hindices.nodup, ?_, ?_⟩
  · simpa using selectedClauses_length_of_valid F words hvalid
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
    exact ExecCNF.mem_formulaSet.mpr ⟨D, hsub hD, rfl⟩

/-- Any tuple with the witness values reaches the required reversed clause family. -/
theorem selectedClauses_of_values (F : List (List (List Bool)))
    (S : Finset (Finset (List Bool))) (words : List (List Bool))
    (hF : (F.map ExecCNF.clauseSet).Nodup) (hS : S ⊆ ExecCNF.formulaSet F)
    (hvalues : words.map CounterPrograms.value = familyIndices F S) :
    (words.map CounterPrograms.value).Pairwise (· < ·) ∧
      (∀ word ∈ words, CounterPrograms.value word < F.length) ∧
      words.length = S.card ∧
      (ExecSelectedFamilyProgram.selectedClauses F words).length = words.length ∧
      ExecCNF.formulaSet (ExecSelectedFamilyProgram.selectedClauses F words).reverse = S ∧
      ((ExecSelectedFamilyProgram.selectedClauses F words).reverse.map
        ExecCNF.clauseSet).Nodup := by
  have hg : ExecSelectedFamilyProgram.selectedClauses F words =
      gather F (familyIndices F S) := by rw [selectedClauses_eq_gather, hvalues]
  have hl : words.length = (familyIndices F S).length := by
    simpa using congrArg List.length hvalues
  refine ⟨hvalues.symm ▸ familyIndices_increasing F S, ?_,
    hl.trans (familyIndices_length F S hF hS), ?_, ?_, ?_⟩
  · intro word hw
    apply familyIndices_lt_length F S
    rw [← hvalues]
    exact List.mem_map.mpr ⟨word, hw, rfl⟩
  · rw [hg, hl]
    exact gather_selectIndices_length _ _
  · rw [hg]
    exact gather_familyIndices_formulaSet F S hS
  · rw [hg]
    exact gather_familyIndices_nodup F S hF

end SubexponentialSAT.ExecSelectedFamilyCompleteness

end OAI.Algorithms
