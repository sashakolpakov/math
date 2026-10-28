import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgramReady

namespace OAI.Algorithms

/-! The checked loader boundary consumed by the actual packing selector. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem program_ready (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List Bool) (n k f : ℕ) (raw : List PairScoreProgram.PlanPair)
    (h60 : outside 60=[]) (hr : 0 < SubexponentialSAT.BinaryArithmetic.toNat (outside 59)) :
    let r := SubexponentialSAT.BinaryArithmetic.toNat (outside 59)
    let Q := SubexponentialSAT.BinaryArithmetic.toNat (outside 55)
    ∃ a : Word r Q, ∃ tail : List (Word r Q), ∃ rf,
      (a::tail).Nodup ∧ (∀ w,w∈a::tail) ∧
      let d := readyLocal rf r Q n f (PairScoreProgram.pairRecords raw)
        (outside 56) (outside 57) (outside 58) (outside 59)
      RunsIn program (budget outside scopes n k f (PairScoreProgram.pairRecords raw))
        ((rawInput outside regs scopes n k f (PairScoreProgram.pairRecords raw)).withPC
          (some program.entry))
        ((framed (Function.update outside 60 scopes) d).withPC none) ∧
      SequentialProgram.Memory ReadPlan.encodeWord a tail (n+f) [] d.stacks ∧
      (d.stacks 11).length=n+f ∧
      SequentialProgram.HighState
        (PackingProgram.Assembly.environment (ScoreBuilderRawInput.environment 1 (a::tail) (n+f) raw)
          (outside 56) (outside 57) (outside 58) (outside 59)) d.stacks := by
  dsimp only
  obtain ⟨a,tail,hrows,hn,hall⟩ := AssignmentAlphabetSemantics.wordBytes_order hr
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55))
  obtain ⟨rf,htrace⟩ := program_run outside regs scopes n k f
    (PairScoreProgram.pairRecords raw) h60 hr
  exact ⟨a,tail,rf,hn,hall,htrace,
    ready_memory rf a tail hrows n f _ _ _ _ _,
    ready_remaining rf _ _ n f _ _ _ _ _,
    ready_high rf a tail hrows n f raw _ _ _ _⟩

theorem output_master (outside : Store) (scopes : List Bool) (d : State 16 48) :
    (framed (Function.update outside 60 scopes) d).stacks 60=scopes := by
  rw [framed_outside _ d 60 (by decide),Function.update_self]

theorem output_metadata (outside : Store) (scopes : List Bool) (d : State 16 48)
    (i : Fin 64) (hi : 48 ≤ i.val) (h60 : i≠60) :
    (framed (Function.update outside 60 scopes) d).stacks i=outside i := by
  have hout : ¬ ∃ j,lowPorts j=i := by
    rintro ⟨j,hj⟩
    have he := congrArg Fin.val hj
    change j.val=i.val at he
    have := j.isLt
    omega
  rw [framed_outside _ d i hout,Function.update_of_ne h60]

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
