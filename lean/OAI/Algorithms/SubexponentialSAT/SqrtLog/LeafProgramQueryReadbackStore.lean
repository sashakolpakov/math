import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReadbackWide

namespace OAI.Algorithms

/-! Exact wide-store restoration for count readback.  Parser and odometer
registers are preserved even though the reusable narrow ABI includes them. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT BitProgram StructuredCalls

noncomputable def completed (a : Data) (regs : Fin 8 → Bool) (word : List Bool) : Data :=
  install a (QueryReadback.finish (project a) regs word (a.stacks 194) (a.stacks 202))

def changed : List (Fin 768) := [261,323,324,325,326,327,328,329]

theorem completed_frame (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (i : Fin 768) (hi : i∉changed) : (completed a regs word).stacks i=a.stacks i := by
  by_cases h194 : i=194
  · subst i
    have h := (QueryReadback.finish_metadata (project a) regs word (a.stacks 194) (a.stacks 202)).1
    exact (embedState_stack regMap stackMap a _ stackMap_injective 194).trans h
  by_cases h202 : i=202
  · subst i
    have h := (QueryReadback.finish_metadata (project a) regs word (a.stacks 194) (a.stacks 202)).2
    exact (embedState_stack regMap stackMap a _ stackMap_injective 202).trans h
  apply finished_stack_frame
  simp only [changed,List.mem_cons,List.mem_nil_iff,or_false] at hi ⊢
  tauto

theorem completed_output (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (hs : a.stacks 323=[]) (ht : a.stacks 324=[]) :
    (completed a regs word).stacks 323=word := by
  exact (embedState_stack regMap stackMap a _ stackMap_injective 323).trans
    (QueryReadback.finish_output (project a) regs word (a.stacks 194) (a.stacks 202) hs ht)

theorem completed_scratch (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (i : Fin 768) (hi : i∈([261,324,325,326,327,328,329] : List (Fin 768))) :
    (completed a regs word).stacks i=[] := by
  have localProof (j : Fin 330)
      (hj : j ∈ ([261,324,325,326,327,328,329] : List (Fin 330))) :
      (completed a regs word).stacks (stackMap j) = [] :=
    (embedState_stack regMap stackMap a _ stackMap_injective j).trans
      (QueryReadback.finish_scratch (project a) regs word (a.stacks 194) (a.stacks 202) j hj)
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst i
  · exact localProof 261 (by simp)
  · exact localProof 324 (by simp)
  · exact localProof 325 (by simp)
  · exact localProof 326 (by simp)
  · exact localProof 327 (by simp)
  · exact localProof 328 (by simp)
  · exact localProof 329 (by simp)

theorem completed_register_frame (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) : (completed a regs word).regs i=a.regs i := by
  by_cases hsmall : i.val < 19
  · let j : Fin 19 := ⟨i.val,hsmall⟩
    have hji : regMap j=i := Fin.ext rfl
    rw [← hji]
    exact (embedState_register regMap stackMap a _ regMap_injective j).trans
      (QueryReadback.finish_register_frame (project a) regs word (a.stacks 194) (a.stacks 202)
        j hi)
  · exact register_outside a _ i (by omega)

/-- All reader temporaries were blank before the call. Thus only its source
coefficient and output count differ at return. -/
theorem completed_stacks (a : Data) (regs : Fin 8 → Bool) (word : List Bool)
    (hempty : ∀ i∈([323,324,325,326,327,328,329] : List (Fin 768)), a.stacks i=[]) :
    (completed a regs word).stacks=Function.update (Function.update a.stacks 261 []) 323 word := by
  funext i
  by_cases h261 : i=261
  · subst i
    simp [completed_scratch a regs word 261 (by simp)]
  by_cases h323 : i=323
  · subst i
    simp [completed_output a regs word (hempty 323 (by simp)) (hempty 324 (by simp))]
  by_cases hwork : i∈([324,325,326,327,328,329] : List (Fin 768))
  · rw [completed_scratch a regs word i (by simpa using Or.inr hwork)]
    simp [h261,h323,hempty i (by simpa using Or.inr hwork)]
  · rw [completed_frame a regs word i]
    · simp [h261,h323]
    · simpa [changed,h261,h323] using hwork

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
