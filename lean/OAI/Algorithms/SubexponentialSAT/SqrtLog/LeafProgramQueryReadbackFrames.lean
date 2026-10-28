import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReadback

namespace OAI.Algorithms

/-! Frame and cleanup facts for the physical CRT count reader. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

noncomputable def finish (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) : Data :=
  afterMove (install a ⟨regs, store word modulus [] width⟩)

theorem finish_output (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) (hs : a.stacks 323 = []) (ht : a.stacks 324 = []) :
    (finish a regs word modulus width).stacks 323 = word := by
  have h323 : (install a ⟨regs, store word modulus [] width⟩).stacks 323 = [] := by
    rw [show (install a ⟨regs, store word modulus [] width⟩).stacks 323 = a.stacks 323 from
      embedState_stack_frame _ _ _ _ _ (by decide)]
    exact hs
  have h324 : (install a ⟨regs, store word modulus [] width⟩).stacks 324 = [] := by
    rw [show (install a ⟨regs, store word modulus [] width⟩).stacks 324 = a.stacks 324 from
      embedState_stack_frame _ _ _ _ _ (by decide)]
    exact ht
  rw [finish, afterMove_output _ h323 h324]
  exact embedState_stack regMap stackMap a _ stackMap_injective 0

theorem finish_register_frame (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) (i : Fin 19) (hi : 8 ≤ i.val) :
    (finish a regs word modulus width).regs i = a.regs i := by
  have h0 : i ≠ 0 := by intro h; subst i; simp at hi
  have h1 : i ≠ 1 := by intro h; subst i; simp at hi
  change (readRegs (install a ⟨regs, store word modulus [] width⟩).regs 0 1 none) i = _
  simp only [readRegs, Function.update_of_ne h1, Function.update_of_ne h0]
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem finish_stack_frame (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) (i : Fin 330)
    (hi : i ∉ ([194, 202, 261, 323, 324, 325, 326, 327, 328, 329] : List (Fin 330))) :
    (finish a regs word modulus width).stacks i = a.stacks i := by
  have h261 : i ≠ 261 := by intro h; subst i; simp at hi
  have h323 : i ≠ 323 := by intro h; subst i; simp at hi
  have h324 : i ≠ 324 := by intro h; subst i; simp at hi
  rw [finish, afterMove_frame _ _ h261 h323 h324]
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  apply hi
  rw [← hj]
  fin_cases j <;> simp [stackMap]

theorem finish_metadata (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) :
    (finish a regs word modulus width).stacks 194 = modulus ∧
    (finish a regs word modulus width).stacks 202 = width := by
  constructor
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 5
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 7

theorem finish_scratch (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) (i : Fin 330)
    (hi : i ∈ ([261, 324, 325, 326, 327, 328, 329] : List (Fin 330))) :
    (finish a regs word modulus width).stacks i = [] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with h | h | h | h | h | h | h <;> subst i
  · simp [finish, afterMove, StackRoutines.transferStacks]
  · exact afterMove_scratch _
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 1
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 2
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 3
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 4
  · rw [finish, afterMove_frame _ _ (by decide) (by decide) (by decide)]
    exact embedState_stack regMap stackMap a _ stackMap_injective 6

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
