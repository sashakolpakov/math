import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def cacheTapes (a : LocalData) : Fin 768 → List Bool :=
  Function.update (Function.update (copyManyState directCopies a).stacks 69 (rawOne a.stacks))
    167 (rawOne a.stacks)

private theorem copies_append (ps qs : List (Fin 768 × Fin 768)) (a : LocalData) :
    copyManyState (ps++qs) a = copyManyState qs (copyManyState ps a) := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨src,dst⟩
      exact ih _

private theorem direct_frame (a : LocalData) (i : Fin 768)
    (hi : i ∉ cachePorts) : (copyManyState directCopies a).stacks i = a.stacks i := by
  apply copyMany_frame
  intro p hp he
  have hmem : p.2∈cachePorts := (show ∀ p∈directCopies, p.2∈cachePorts by simp [directCopies,cachePorts]) p hp
  exact hi (he.symm ▸ hmem)

theorem cache_frame (a : LocalData) (i : Fin 768) (hi : i ∉ cachePorts) :
    cacheTapes a i = a.stacks i := by
  have h69 : i≠69 := fun he => hi (by simp [cachePorts,he])
  have h167 : i≠167 := fun he => hi (by simp [cachePorts,he])
  simpa only [cacheTapes,Function.update_of_ne h69,Function.update_of_ne h167] using direct_frame a i hi

theorem cache_direct (a : LocalData) (h : Ready a.stacks)
    (p : Fin 768 × Fin 768) (hp : p∈directCopies) : cacheTapes a p.2 = a.stacks p.1 := by
  have hp69 : p.2≠69 := (show ∀ p∈directCopies,p.2≠69 by simp [directCopies]) p hp
  have hp167 : p.2≠167 := (show ∀ p∈directCopies,p.2≠167 by simp [directCopies]) p hp
  simp only [cacheTapes,Function.update_of_ne hp69,Function.update_of_ne hp167]
  apply copyMany_value directCopies a (by decide) _ (by simp [directCopies]) p hp
  intro q hq
  exact h q.2 ((show ∀ q∈directCopies,q.2∈cachePorts++pocket by simp [directCopies,cachePorts,pocket]) q hq)

theorem cache_one (a : LocalData) : cacheTapes a 69=rawOne a.stacks ∧
    cacheTapes a 167=rawOne a.stacks := by simp [cacheTapes]

/-- The asserted update store includes every cache byte and all external tapes. -/
theorem final_stacks (a : LocalData) (h : Ready a.stacks) (rr : Fin 8 → Bool) :
    (finalState (prepared a) rr (rawOne a.stacks)).stacks = cacheTapes a := by
  funext i
  have h69 := h 69 (by decide)
  have h167 := h 167 (by decide)
  have hf69 : (copyManyState directCopies a).stacks 69=[] := (copyMany_frame directCopies a 69 (by simp [directCopies])).trans h69
  have hf167 : (copyManyState directCopies a).stacks 167=[] := (copyMany_frame directCopies a 167 (by simp [directCopies])).trans h167
  by_cases hi69 : i=69
  · subst i
    simp [finalState,prepared,copies,copies_append,copyManyState,copyState,clearState,
      StackRoutines.copyStacks,constantResult,constantTapes,cacheTapes,hf69]
  by_cases hi167 : i=167
  · subst i
    simp [finalState,prepared,copies,copies_append,copyManyState,copyState,clearState,
      StackRoutines.copyStacks,constantResult,constantTapes,cacheTapes,hf167]
  by_cases hr : 340 ≤ i.val ∧ i.val ≤ 345
  · have hi : i=340 ∨ i=341 ∨ i=342 ∨ i=343 ∨ i=344 ∨ i=345 := by
      have : i.val=340 ∨ i.val=341 ∨ i.val=342 ∨ i.val=343 ∨ i.val=344 ∨ i.val=345 := by omega
      simpa [Fin.ext_iff] using this
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 340 (by decide),h 340 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 341 (by decide),h 341 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 342 (by decide),h 342 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 343 (by decide),h 343 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 344 (by decide),h 344 (by decide)]
    · simp [finalState,copyManyState,copyState,clearState,StackRoutines.copyStacks,
        constantResult,constantTapes,cacheTapes,direct_frame a 345 (by decide),h 345 (by decide)]
  · have h340 : i≠340 := by intro he; subst i; simp at hr
    have h343 : i≠343 := by intro he; subst i; simp at hr
    have h345 : i≠345 := by intro he; subst i; simp at hr
    have hr' : ¬(340 ≤ i.val ∧ i.val < 345) := by omega
    simp [finalState,prepared,copies,copies_append,copyManyState,copyState,clearState,
      StackRoutines.copyStacks,constantResult,constantTapes,cacheTapes,hi69,hi167,h340,h343,h345,hr']

theorem local_eval_exact (a : LocalData) (h : Ready a.stacks) :
    ∃ b, Eval localCommand (localBudget a) a b ∧ b.stacks=cacheTapes a := by
  obtain ⟨rr,he⟩ := local_eval a h
  exact ⟨_,he,final_stacks a h rr⟩

/-- Only the staged low cache bank is cleared on exit. -/
abbrev localCleanup : Cmd 16 768 := clearMany cachePorts

theorem local_cleanup (a : LocalData) :
    Eval localCleanup (clearManyCost cachePorts a) a (clearManyState cachePorts a) :=
  clearMany_eval cachePorts a

theorem cleanup_restores (a b : LocalData) (h : Ready a.stacks) (hb : b.stacks=cacheTapes a) :
    (clearManyState cachePorts b).stacks = a.stacks := by
  funext i
  rw [clearMany_stacks]
  by_cases hi : i∈cachePorts
  · rw [ite_eq_left hi]
    exact (h i (List.mem_append_left _ hi)).symm
  · rw [ite_eq_right hi,hb,cache_frame a i hi]

theorem rawOne_length (a : LocalData) :
    (rawOne a.stacks).length = 2*(a.stacks 128).length+2*(a.stacks 207).length+6 := by
  simp [rawOne,HashCircuitProgram.Constant.key,Encoding.length_frame]
  omega

/-- Linear in a bound on actual source words, including the generated raw one. -/
theorem localBudget_le (a : LocalData) (B : ℕ) (ha : WordBound B a) :
    localBudget a  ≤  1000*(B+1) := by
  have hc := copyManyCost_le copies a B (by simp [copies,directCopies]) (fun p _ => ha p.1)
  have hn := ha 128
  have ho := ha 207
  rw [show copies.length=14 from rfl] at hc
  unfold localBudget
  rw [rawOne_length]
  omega

end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
