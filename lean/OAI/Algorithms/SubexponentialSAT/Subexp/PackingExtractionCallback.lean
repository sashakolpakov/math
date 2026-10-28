import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionEmit

namespace OAI.Algorithms

/-! One actual bucket-record callback: select its indexed vertex and emit it. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

def ports : RecordPrograms.Ports 8 19 :=
  ⟨5, 6, 7, 7, 8, by decide, by decide, by decide, by decide⟩

def finishRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 false) 6 true) 7 false

abbrev callback : Cmd 8 19 :=
  .seq (transfer 8 0)
    (.seq (MatrixProgramSupport.copy 10 2 9)
      (.seq selectCall
        (.seq emitCall
          (.seq (.base (.atom (.set 5 false)))
            (.seq (.base (.atom (.set 6 true))) (.base (.atom (.set 7 false))))))))

def bucketWord (key : List Bool) (bucket : List (List Bool)) : List Bool :=
  Encoding.frame key ++ words bucket

def callbackBudget (payload block address : List Bool) : ℕ :=
  100 * (payload.length + block.length + address.length + 2)

theorem callback_eval (key vertex : List Bool) (pre rest : List (List Bool))
    (c : Context) (hblock : c.block = List.replicate pre.length true)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ callbackBudget (bucketWord key (pre ++ vertex :: rest)) c.block c.address,
      ∃ rf, Eval callback n
        (ready regs { c with payload := (bucketWord key (pre ++ vertex :: rest)).reverse })
        (ready (finishRegs rf) (emitted { c with payload := [] } key vertex)) := by
  let payload := bucketWord key (pre ++ vertex :: rest)
  let clean := { c with payload := [] }
  obtain ⟨a, ha, hsa⟩ := transfer_eval (8 : Fin 19) 0 (by decide)
    (ready regs { c with payload := payload.reverse })
  have hea : a = state a.regs clean payload [] [] [] [] [] [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext i
    fin_cases i <;> simp [ready, state, clean, StackRoutines.transferStacks]
  rw [hea] at ha
  obtain ⟨b, hb, hsb⟩ := MatrixProgramSupport.copy_eval (10 : Fin 19) 2 9
    (by decide) (by decide) (by decide)
    (state a.regs clean payload [] [] [] [] [] [] []) rfl
  have heb : b = state b.regs clean payload [] (List.replicate pre.length true)
      [] [] [] [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsb]
    funext i
    fin_cases i <;> simp [state, clean, StackRoutines.copyStacks, hblock]
  rw [heb] at hb
  obtain ⟨ns, hns, rs, hs⟩ := selectCall_eval key vertex pre rest b.regs clean
  obtain ⟨re, he⟩ := emitCall_eval clean key vertex rs
  have hf : Eval (.seq (.base (.atom (.set 5 false)))
      (.seq (.base (.atom (.set 6 true))) (.base (.atom (.set 7 false))))) 3
      (ready re (emitted clean key vertex))
      (ready (finishRegs re) (emitted clean key vertex)) :=
    (Eval.base (.atom _ _)).seq ((Eval.base (.atom _ _)).seq (Eval.base (.atom _ _)))
  let n := (3 * payload.length + 3) + ((7 * c.block.length + 5) +
    (ns + ((PackingEntryEmitter.commandCost vertex key c.block c.address + 1) + 3)))
  refine ⟨n, ?_, re, ?_⟩
  · have hp : payload.length = 2 * key.length + 1 +
        ((words pre).length + (2 * vertex.length + 1 + (words rest).length)) := by
      simp only [payload, bucketWord, PackingBucketSelect.words_append, words,
        List.length_append, Encoding.length_frame]
    dsimp only [n, callbackBudget, PackingEntryEmitter.commandCost]
    change ns ≤ 21 * (payload.length + 1) at hns
    change (3 * payload.length + 3) + ((7 * c.block.length + 5) +
      (ns + ((44 * vertex.length + 24 * key.length + 31 * c.block.length +
        15 * c.address.length + 115 + 1) + 3))) ≤
      100 * (payload.length + c.block.length + c.address.length + 2)
    omega
  · have hrun := ha.seq (hb.seq (hs.seq (he.seq hf)))
    change Eval callback
      ((3 * payload.reverse.length + 3) + ((7 * c.block.length + 5) +
        (ns + ((PackingEntryEmitter.commandCost vertex key c.block c.address + 1) + 3))))
      (ready regs { c with payload := payload.reverse })
      (ready (finishRegs re) (emitted clean key vertex)) at hrun
    simpa only [n, List.length_reverse] using hrun

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
