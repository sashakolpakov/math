import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramFlatProject

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flat_stack_injective : Function.Injective flatStacks := by decide

theorem flat_reg_ports (regs : Fin 4 → Bool) :
    ∀ i, flatOutRegs regs (flatRegs i) = (![false,false,false] : Fin 3 → Bool) i := by
  refine Fin.cases ?_ ?_
  · rfl
  refine Fin.cases ?_ ?_
  · rfl
  refine Fin.cases ?_ ?_
  · rfl
  intro i; exact Fin.elim0 i

theorem flat_reg_frame (regs : Fin 4 → Bool) :
    ∀ i, (¬ ∃ j, flatRegs j = i) → flatOutRegs regs i = regs i := by
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨0,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨1,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨2,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro _; rfl
  intro i; exact Fin.elim0 i

theorem flat_stack_ports (counter mask forward high : List Bool) :
    ∀ i, tapes counter mask forward [] [] [] high [] [] [] (flatStacks i) =
      (![[],[],high] : Fin 3 → List Bool) i := by
  refine Fin.cases ?_ ?_
  · rfl
  refine Fin.cases ?_ ?_
  · rfl
  refine Fin.cases ?_ ?_
  · rfl
  intro i; exact Fin.elim0 i

theorem flat_stack_frame (counter mask forward high : List Bool) :
    ∀ i, (¬ ∃ j, flatStacks j = i) →
      tapes counter mask forward [] [] [] high [] [] [] i =
      tapes counter mask forward [] counter [] [] [] [] [] i := by
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨0,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨1,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro hi; exact (hi ⟨2,rfl⟩).elim
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  refine Fin.cases ?_ ?_
  · intro _; rfl
  intro i; exact Fin.elim0 i

end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
