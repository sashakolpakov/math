import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgramFinish
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyMetadata

namespace OAI.Algorithms

/-! Exact selector memory and environment from the physically generated
alphabet, retaining all ambient head addresses before factor addresses. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem readyLocal_low (regs : Fin 16 → Bool) (r Q n f : ℕ)
    (pairs nb sb mb rb : List Bool) (i : Fin 48) (hi : i.val < 20) :
    (readyLocal regs r Q n f pairs nb sb mb rb).stacks i =
      (AssignmentInitProgram.outputState (context r Q n f pairs)).stacks i := by
  have hs : i≠20 ∧ i≠21 ∧ i≠22 ∧ i≠23 ∧ i≠34 := by
    constructor <;> try (intro h; subst i; norm_num at hi)
    constructor <;> try (intro h; subst i; norm_num at hi)
    constructor <;> try (intro h; subst i; norm_num at hi)
    constructor <;> (intro h; subst i; norm_num at hi)
  simp [readyLocal,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2]

theorem ready_memory (regs : Fin 16 → Bool) {r Q : ℕ}
    (a : Word r Q) (tail : List (Word r Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes r Q)
    (n f : ℕ) (pairs nb sb mb rb : List Bool) :
    SequentialProgram.Memory ReadPlan.encodeWord a tail (n+f) []
      (readyLocal regs r Q n f pairs nb sb mb rb).stacks := by
  have hm := AssignmentInitProgram.output_memory ReadPlan.encodeWord a tail
    (context r Q n f pairs)
    (by simp [context,AssignmentInputProgram.context,←hrows])
    (by simp [context,AssignmentInputProgram.context,←hrows])
    (by simp [context,AssignmentInputProgram.context,AssignmentInputProgram.unary,
      ReadPlan.encodeWord_length,ReadPlan.wordWidth])
  have hc : (context r Q n f pairs).seedCount=n+f := by
    simp [context,AssignmentInputProgram.context,AssignmentInputProgram.seedCount,Nat.add_comm]
  rw [hc] at hm
  constructor
  · simpa [readyLocal] using hm.assignment
  · simpa [readyLocal] using hm.alphabet
  · simpa [readyLocal] using hm.width
  · simpa [readyLocal] using hm.processed
  · intro i hi
    rw [readyLocal_low regs r Q n f pairs nb sb mb rb i
      ((by decide : ∀ i : Fin 48, i∈SequentialProgram.scratchPorts → i.val < 20) i hi)]
    exact hm.scratch i hi

theorem ready_high (regs : Fin 16 → Bool) {r Q : ℕ}
    (a : Word r Q) (tail : List (Word r Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes r Q)
    (n f : ℕ) (raw : List PairScoreProgram.PlanPair) (nb sb mb rb : List Bool) :
    SequentialProgram.HighState
      (PackingProgram.Assembly.environment (ScoreBuilderRawInput.environment 1 (a::tail) (n+f) raw)
        nb sb mb rb)
      (readyLocal regs r Q n f (PairScoreProgram.pairRecords raw) nb sb mb rb).stacks := by
  intro i hi
  fin_cases i <;> first
    | (norm_num at hi; done)
    | simp [readyLocal,PackingProgram.Assembly.environment,ScoreBuilderRawInput.environment,
        ScoreBuilderProgram.environment,AssignmentInitProgram.outputState,AssignmentInitProgram.state,
        context,AssignmentInputProgram.context,AssignmentInputProgram.seedCount,
        AssignmentInputProgram.unary,AssignmentSeedRange.seedRecords,
        PairPreparationProgram.seedBytes,SelectionTableProgram.unary,AssignmentInitProgram.unary,
        ←hrows,Nat.add_comm]
      <;> rfl

@[simp] theorem ready_remaining (regs : Fin 16 → Bool) (r Q n f : ℕ)
    (pairs nb sb mb rb : List Bool) :
    ((readyLocal regs r Q n f pairs nb sb mb rb).stacks 11).length=n+f := by
  simp [readyLocal,AssignmentInitProgram.outputState,AssignmentInitProgram.state,
    context,AssignmentInputProgram.context,AssignmentInputProgram.seedCount,
    AssignmentInitProgram.unary,Nat.add_comm]

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
