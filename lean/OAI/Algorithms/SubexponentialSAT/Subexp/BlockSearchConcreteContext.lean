import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchConcrete
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchOutputContext

namespace OAI.Algorithms

/-! Retained physical inputs available after concrete basis search. -/

namespace SubexponentialSAT.Subexp.BlockSearchConcreteContext

open BitProgram BlockSearchPredicate

theorem retains_with_alphabet (p : ℕ) [Fact p.Prime]
    (alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet) {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool)
    {budget : ℕ} {next : StructuredProgram.State 24 42}
    (run : RunsIn BlockSearchConcrete.program budget
      ((BlockSearchExecution.inputState (BlockCoefficientProgram.context p M)
        (scalarCode p) alphabet N regs).withPC (some BlockSearchConcrete.program.entry))
      (next.withPC none)) :
    BlockSearchOutputContext.Retained (BlockCoefficientProgram.context p M) next :=
  BlockSearchOutputContext.program_retains BlockCoefficientProgram.matrixPair
    (BlockCoefficientProgram.context p M) (scalarCode p) alphabet M
    (BlockCoefficientProgram.coefficientCost p m N) rfl
    (BlockSearchConcrete.coefficientContract_with_alphabet p alphabet hfull M) regs run

theorem retains (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool)
    {budget : ℕ} {next : StructuredProgram.State 24 42}
    (run : RunsIn BlockSearchConcrete.program budget
      ((BlockSearchConcrete.inputState p M regs).withPC (some BlockSearchConcrete.program.entry))
      (next.withPC none)) :
    BlockSearchOutputContext.Retained (BlockCoefficientProgram.context p M) next :=
  retains_with_alphabet p (QuarticSearch.elements p) (QuarticSearch.mem_elements p) M regs run

theorem dimension_with_alphabet (p : ℕ) [Fact p.Prime]
    (alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet) {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool)
    {budget : ℕ} {next : StructuredProgram.State 24 42}
    (run : RunsIn BlockSearchConcrete.program budget
      ((BlockSearchExecution.inputState (BlockCoefficientProgram.context p M)
        (scalarCode p) alphabet N regs).withPC (some BlockSearchConcrete.program.entry))
      (next.withPC none)) : next.stacks 10 = List.replicate N true :=
  (retains_with_alphabet p alphabet hfull M regs run).2.2.2.2

/-- Stack 10 supplies the actual unary dimension needed by the subsequent
table-transpose program. No second construction of this count is required. -/
theorem dimension (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (regs : Fin 24 → Bool)
    {budget : ℕ} {next : StructuredProgram.State 24 42}
    (run : RunsIn BlockSearchConcrete.program budget
      ((BlockSearchConcrete.inputState p M regs).withPC (some BlockSearchConcrete.program.entry))
      (next.withPC none)) : next.stacks 10 = List.replicate N true :=
  (retains p M regs run).2.2.2.2

end SubexponentialSAT.Subexp.BlockSearchConcreteContext

end OAI.Algorithms
