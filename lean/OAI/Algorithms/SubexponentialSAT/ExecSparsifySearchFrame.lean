import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

namespace OAI.Algorithms

/-!
# Local framing and storage bounds after the concrete node search

The search is relocated above the five worklist ports. Its resulting local
state determines every cleanup and child-input copy cost. Arbitrary pending
and leaf streams do not occur in these bounds.
-/

namespace SubexponentialSAT.ExecSparsifySearchFrame

open BitProgram StructuredCalls
open ExecSparsifyNode (port headLoaded)
open ExecSparsifyProgram (searchPort)
open ExecCNFWidthLoad (low)
open scoped BigOperators

noncomputable def searched {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) : ExecSparsifyNode.Data k :=
  embedState id (searchPort k) (headLoaded bits a) b

theorem searched_stack {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) (i : Fin (k + 34)) :
    (searched bits a b).stacks (searchPort k i) = b.stacks i :=
  embedState_stack id (searchPort k) (headLoaded bits a) b
    (ExecSparsifyProgram.searchPort_injective k) i

theorem searched_low {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) (i : Fin 32) :
    (searched bits a b).stacks (port k ⟨5 + i.val, by omega⟩) = b.stacks (low k i) := by
  rw [← ExecSparsifyProgram.searchPort_low]
  exact searched_stack bits a b (low k i)

/-- The complete worklist core is outside the relocated search. -/
theorem searched_core_frame {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k)
    (i : Fin (k + 39)) (hi : i.val < 5) :
    (searched bits a b).stacks i = a.stacks i := by
  have hnot : ¬ ∃ j, searchPort k j = i := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change 5 + j.val = i.val at hv
    omega
  have hh : i ≠ port k 21 := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 21 at hv
    omega
  exact (embedState_stack_frame id (searchPort k) (headLoaded bits a) b i hnot).trans
    (ExecSparsifyNode.headLoaded_stack_frame a bits i hh)

/-- The persistent parameter bank is preserved by the local search frame. -/
theorem searched_parameter_frame {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k)
    (hf : ExecCNFNodeSearch.Frame k
      (projectState id (searchPort k) (headLoaded bits a)) b)
    (i : Fin (k + 39)) (hi : 37 ≤ i.val) :
    (searched bits a b).stacks i = a.stacks i := by
  let j : Fin (k + 34) := ⟨i.val - 5, by have := i.isLt; omega⟩
  have hj : searchPort k j = i := by
    apply Fin.ext
    change 5 + (i.val - 5) = i.val
    omega
  have hne (q : Fin 32) : j ≠ low k q := by
    intro he
    have hv := congrArg Fin.val he
    change i.val - 5 = q.val at hv
    have := q.isLt
    omega
  have hframe := hf j (hne 8) (hne 13) (hne 14) (hne 15)
    (hne 17) (hne 19) (hne 20) (hne 21)
  change b.stacks j = (headLoaded bits a).stacks (searchPort k j) at hframe
  rw [hj] at hframe
  have hsearch : (searched bits a b).stacks i = b.stacks j := by
    simpa only [hj] using searched_stack bits a b j
  have hh : i ≠ port k 21 := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 21 at hv
    omega
  exact hsearch.trans (hframe.trans (ExecSparsifyNode.headLoaded_stack_frame a bits i hh))

/-- The three initial child-copy scratch ports stay empty after search. -/
theorem searched_work_empty {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k)
    (ha : ∀ i : Fin (k + 39), 2 ≤ i.val → i.val < 37 → a.stacks i = [])
    (hf : ExecCNFNodeSearch.Frame k
      (projectState id (searchPort k) (headLoaded bits a)) b)
    (i : Fin (k + 39)) (hi : 5 ≤ i.val ∧ i.val ≤ 7) :
    (searched bits a b).stacks i = [] := by
  let j : Fin (k + 34) := ⟨i.val - 5, by have := i.isLt; omega⟩
  have hj : searchPort k j = i := by
    apply Fin.ext
    change 5 + (i.val - 5) = i.val
    omega
  have hne (q : Fin 32) (hq : 3 ≤ q.val) : j ≠ low k q := by
    intro he
    have hv := congrArg Fin.val he
    change i.val - 5 = q.val at hv
    omega
  have hframe := hf j (hne 8 (by decide)) (hne 13 (by decide))
    (hne 14 (by decide)) (hne 15 (by decide)) (hne 17 (by decide))
    (hne 19 (by decide)) (hne 20 (by decide)) (hne 21 (by decide))
  change b.stacks j = (headLoaded bits a).stacks (searchPort k j) at hframe
  rw [hj] at hframe
  have hsearch : (searched bits a b).stacks i = b.stacks j := by
    simpa only [hj] using searched_stack bits a b j
  have hh : i ≠ port k 21 := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 21 at hv
    omega
  exact hsearch.trans (hframe.trans ((ExecSparsifyNode.headLoaded_stack_frame a bits i hh).trans
    (ha i (by omega) (by omega))))

def localSearchPorts (k : ℕ) : List (Fin (k + 34)) :=
  (List.finRange 32).map (low k)

def transientIndex (i : Fin 30) : Fin 32 := ⟨2 + i.val, by omega⟩

def localTransientPorts (k : ℕ) : List (Fin (k + 34)) :=
  (List.finRange 30).map (fun i => low k (transientIndex i))

def localSearchBits {k : ℕ} (b : ExecCNFNodeSearch.Data k) : ℕ :=
  ((localSearchPorts k).map (fun i => (b.stacks i).length)).sum

def localTransientBits {k : ℕ} (b : ExecCNFNodeSearch.Data k) : ℕ :=
  ((localTransientPorts k).map (fun i => (b.stacks i).length)).sum

def localLoadCost {k : ℕ} (b : ExecCNFNodeSearch.Data k) : ℕ :=
  7 * ((b.stacks (low k 16)).length + (b.stacks (low k 8)).length +
    (b.stacks (low k 13)).length) + 15

theorem transient_port (k : ℕ) (i : Fin 30) :
    searchPort k (low k (transientIndex i)) = port k ⟨7 + i.val, by omega⟩ := by
  apply Fin.ext
  change 5 + (2 + i.val) = 7 + i.val
  omega

theorem searchBits_eq {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.searchBits (searched bits a b) = localSearchBits b := by
  simp only [ExecSparsifyNode.searchBits, ExecSparsifyNode.searchPorts,
    localSearchBits, localSearchPorts, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  rw [searched_low]

theorem transientBits_eq {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.transientBits (searched bits a b) = localTransientBits b := by
  simp only [ExecSparsifyNode.transientBits, ExecSparsifyNode.transientPorts,
    localTransientBits, localTransientPorts, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  rw [← transient_port, searched_stack]

theorem loadCost_eq {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.loadCost (searched bits a b) = localLoadCost b := by
  unfold ExecSparsifyNode.loadCost localLoadCost
  change 7 * (((searched bits a b).stacks (searchPort k (low k 16))).length +
    ((searched bits a b).stacks (searchPort k (low k 8))).length +
    ((searched bits a b).stacks (searchPort k (low k 13))).length) + 15 = _
  rw [searched_stack, searched_stack, searched_stack]

theorem localSearchPorts_nodup (k : ℕ) : (localSearchPorts k).Nodup :=
  (List.nodup_finRange 32).map (ExecCNFWidthLoad.low_injective k)

theorem localTransientPorts_nodup (k : ℕ) : (localTransientPorts k).Nodup := by
  apply (List.nodup_finRange 30).map
  intro i j h
  have hh := ExecCNFWidthLoad.low_injective k h
  apply Fin.ext
  have hv := congrArg Fin.val hh
  change 2 + i.val = 2 + j.val at hv
  omega

theorem mem_localSearchPorts (k : ℕ) (i : Fin 32) :
    low k i ∈ localSearchPorts k :=
  List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

theorem localTransientPorts_subset (k : ℕ) :
    ∀ i ∈ localTransientPorts k, i ∈ localSearchPorts k := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact mem_localSearchPorts k (transientIndex j)

/-- A low-word bound excludes every persistent bank and cache port. -/
theorem low_word_length_le {k : ℕ} (b : ExecCNFNodeSearch.Data k) (i : Fin 32) :
    (b.stacks (low k i)).length ≤ localSearchBits b := by
  unfold localSearchBits
  rw [← List.sum_toFinset (fun j => (b.stacks j).length) (localSearchPorts_nodup k)]
  exact Finset.single_le_sum (f := fun j => (b.stacks j).length)
    (fun j _ => Nat.zero_le (b.stacks j).length)
    (List.mem_toFinset.mpr (mem_localSearchPorts k i))

theorem localTransientBits_le_localSearchBits {k : ℕ} (b : ExecCNFNodeSearch.Data k) :
    localTransientBits b ≤ localSearchBits b := by
  unfold localTransientBits localSearchBits
  rw [← List.sum_toFinset (fun j => (b.stacks j).length) (localTransientPorts_nodup k),
    ← List.sum_toFinset (fun j => (b.stacks j).length) (localSearchPorts_nodup k)]
  apply Finset.sum_le_sum_of_subset
  intro i hi
  exact List.mem_toFinset.mpr (localTransientPorts_subset k i (List.mem_toFinset.mp hi))

theorem list_stack_bits_le {s : ℕ} (stk : Fin s → List Bool)
    (ports : List (Fin s)) (hn : ports.Nodup) :
    (ports.map (fun i => (stk i).length)).sum ≤ stackBits stk := by
  rw [← List.sum_toFinset (fun i => (stk i).length) hn]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem stack_length_le {s : ℕ} (stk : Fin s → List Bool) (i : Fin s) :
    (stk i).length ≤ stackBits stk := by
  unfold stackBits
  exact Finset.single_le_sum (f := fun j => (stk j).length)
    (fun j _ => Nat.zero_le (stk j).length) (Finset.mem_univ i)

theorem searchBits_le {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.searchBits (searched bits a b) ≤ stackBits b.stacks := by
  rw [searchBits_eq]
  exact list_stack_bits_le b.stacks _ (localSearchPorts_nodup k)

theorem transientBits_le {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.transientBits (searched bits a b) ≤ stackBits b.stacks := by
  rw [transientBits_eq]
  exact list_stack_bits_le b.stacks _ (localTransientPorts_nodup k)

theorem loadCost_le {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.loadCost (searched bits a b) ≤ 21 * stackBits b.stacks + 15 := by
  rw [loadCost_eq]
  have h16 := stack_length_le b.stacks (low k 16)
  have h8 := stack_length_le b.stacks (low k 8)
  have h13 := stack_length_le b.stacks (low k 13)
  unfold localLoadCost
  omega

theorem prepareCost_le {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.prepareCost (searched bits a b) ≤ 23 * stackBits b.stacks + 105 := by
  have hl := loadCost_le bits a b
  have ht := transientBits_le bits a b
  unfold ExecSparsifyNode.prepareCost
  omega

theorem terminalCost_le {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.terminalCost (searched bits a b) ≤ 2 * stackBits b.stacks + 129 := by
  have hs := searchBits_le bits a b
  unfold ExecSparsifyNode.terminalCost
  omega

/-- The sharper cleanup bound counts only the thirty-two transient search
ports; arbitrary persistent data above them is excluded. -/
theorem transientBits_le_local {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.transientBits (searched bits a b) ≤ localSearchBits b := by
  rw [transientBits_eq]
  exact localTransientBits_le_localSearchBits b

theorem loadCost_le_local {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.loadCost (searched bits a b) ≤ 21 * localSearchBits b + 15 := by
  rw [loadCost_eq]
  have h16 := low_word_length_le b 16
  have h8 := low_word_length_le b 8
  have h13 := low_word_length_le b 13
  unfold localLoadCost
  omega

theorem prepareCost_le_local {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.prepareCost (searched bits a b) ≤ 23 * localSearchBits b + 105 := by
  have hl := loadCost_le_local bits a b
  have ht := transientBits_le_local bits a b
  unfold ExecSparsifyNode.prepareCost
  omega

theorem terminalCost_le_local {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.terminalCost (searched bits a b) ≤ 2 * localSearchBits b + 129 := by
  simp only [ExecSparsifyNode.terminalCost, searchBits_eq, le_refl]

/-- This uses the actual selected-port growth theorem: even an instruction
that modifies a persistent port cannot allocate more than one low-block bit.
No frame or size assumption on the high ports is needed. -/
theorem localSearchBits_trace_le {k : ℕ} (a b : ExecCNFNodeSearch.Data k) {t : ℕ}
    (htrace : Trace (ExecCNFNodeSearch.program k) t
      (a.withPC (some (ExecCNFNodeSearch.program k).entry)) (b.withPC none)) :
    localSearchBits b ≤ localSearchBits a + t := by
  have h := BitProgram.trace_listStackBits (ExecCNFNodeSearch.program k)
    (localSearchPorts k) (localSearchPorts_nodup k)
    (a := a.withPC (some (ExecCNFNodeSearch.program k).entry))
    (b := b.withPC none) (n := t) htrace
  change localSearchBits b ≤ localSearchBits a + t at h
  exact h

theorem localSearchBits_runsIn_le {k : ℕ} (a b : ExecCNFNodeSearch.Data k) {bound : ℕ}
    (hrun : RunsIn (ExecCNFNodeSearch.program k) bound
      (a.withPC (some (ExecCNFNodeSearch.program k).entry)) (b.withPC none)) :
    localSearchBits b ≤ localSearchBits a + bound := by
  have h := BitProgram.runsIn_listStackBits (ExecCNFNodeSearch.program k)
    (localSearchPorts k) (localSearchPorts_nodup k)
    (a := a.withPC (some (ExecCNFNodeSearch.program k).entry))
    (b := b.withPC none) (n := bound) hrun
  change localSearchBits b ≤ localSearchBits a + bound at h
  exact h

/-- At the real clean entry, only the copied formula occupies the low
search block. Persistent parameters and caches do not contribute. -/
theorem localSearchBits_initial {k : ℕ} (bits : List Bool)
    (a : ExecSparsifyNode.Data k)
    (ha : ∀ i : Fin (k + 39), 2 ≤ i.val → i.val < 37 → a.stacks i = []) :
    localSearchBits (projectState id (searchPort k) (headLoaded bits a)) = bits.length := by
  let p := projectState id (searchPort k) (headLoaded bits a)
  have hlow (i : Fin 32) : p.stacks (low k i) = if i = 16 then bits else [] := by
    change (headLoaded bits a).stacks (searchPort k (low k i)) = _
    by_cases hi : i = 16
    · subst i
      change Function.update a.stacks (port k 21) bits (port k 21) = bits
      simp
    · have hp : port k ⟨5 + i.val, by omega⟩ ≠ port k 21 := by
        intro he
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val he
        change 5 + i.val = 21 at hv
        omega
      rw [ite_eq_right hi, ExecSparsifyProgram.searchPort_low,
        ExecSparsifyNode.headLoaded_stack_frame a bits _ hp]
      apply ha
      · change 2 ≤ 5 + i.val
        omega
      · change 5 + i.val < 37
        have := i.isLt
        omega
  change localSearchBits p = bits.length
  simp only [localSearchBits, localSearchPorts, List.map_map, Function.comp_def]
  rw [← Fin.sum_univ_def]
  simp [hlow, apply_ite]

/-- Neither the previous head encoding nor any outside stack contents enter
the cleanup and child-input-copy cost. -/
theorem costs_independent {k : ℕ} (bits₁ bits₂ : List Bool)
    (a₁ a₂ : ExecSparsifyNode.Data k) (b : ExecCNFNodeSearch.Data k) :
    ExecSparsifyNode.searchBits (searched bits₁ a₁ b) =
        ExecSparsifyNode.searchBits (searched bits₂ a₂ b) ∧
      ExecSparsifyNode.transientBits (searched bits₁ a₁ b) =
        ExecSparsifyNode.transientBits (searched bits₂ a₂ b) ∧
      ExecSparsifyNode.loadCost (searched bits₁ a₁ b) =
        ExecSparsifyNode.loadCost (searched bits₂ a₂ b) := by
  simp only [searchBits_eq, transientBits_eq, loadCost_eq, and_self]

end SubexponentialSAT.ExecSparsifySearchFrame

end OAI.Algorithms
