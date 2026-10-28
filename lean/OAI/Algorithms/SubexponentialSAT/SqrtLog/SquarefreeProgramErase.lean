import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramCompare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramFrame

namespace OAI.Algorithms

/-! Concrete one-record deletion for sparse coefficient dictionaries. The
selected key is saved before comparison; retained records are emitted intact. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev eraseData (regs : Fin 5 → Bool) (source query output saved : List Bool) : StorageData :=
  extendStorage (recordState regs source [] query.reverse [] [] output) saved

def frameRegPorts : Fin 3 → Fin 5 := Fin.castAdd 2
def frameStackPorts : Fin 2 → Fin 7 := ![6,5]

theorem frameRegPorts_injective : Function.Injective frameRegPorts := Fin.castAdd_injective _ _
theorem frameStackPorts_injective : Function.Injective frameStackPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [frameStackPorts]

abbrev emitSaved : Cmd 5 7 := .call
  (ProgramLinking.liftProgram frameEmitProgram frameRegPorts frameStackPorts)

theorem emitSaved_eval (regs : Fin 5 → Bool) (source query output key : List Bool) :
    ∃ final, Eval emitSaved (4 * key.length + 6)
      (eraseData regs source query output key.reverse)
      (eraseData final source query (Encoding.frame key ++ output) []) := by
  let d := eraseData regs source query output key.reverse
  obtain ⟨rr, ht⟩ := frameEmit_trace key output (regs ∘ frameRegPorts)
  let b := frameData rr [] (Encoding.frame key ++ output)
  let final := (embedState frameRegPorts frameStackPorts d b).regs
  have ha : embedState frameRegPorts frameStackPorts d
      (frameData (regs ∘ frameRegPorts) key.reverse output) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegPorts_injective frameStackPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [d, frameData, frameStackPorts, extendStorage, storage]
    · intros; rfl
  have hb : embedState frameRegPorts frameStackPorts d b =
      eraseData final source query (Encoding.frame key ++ output) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegPorts_injective frameStackPorts_injective
    · intro i
      exact embedState_register frameRegPorts frameStackPorts d b frameRegPorts_injective i
    · intro i hi
      exact embedState_register_frame frameRegPorts frameStackPorts d b i hi
    · intro i; fin_cases i <;> simp [b, eraseData, frameData, frameStackPorts, extendStorage, storage]
    · intro i hi
      fin_cases i <;> simp_all [d, eraseData, frameStackPorts, extendStorage, storage,
        Fin.exists_fin_succ]
  refine ⟨final, ?_⟩
  have he := eval_call_lifted frameEmitProgram frameRegPorts frameStackPorts d
    frameRegPorts_injective frameStackPorts_injective ht
  change Eval emitSaved (4 * key.length + 6)
    (embedState frameRegPorts frameStackPorts d (frameData (regs ∘ frameRegPorts) key.reverse output))
    (embedState frameRegPorts frameStackPorts d b) at he
  rw [ha,hb] at he
  exact he

abbrev eraseKeep : Cmd 5 7 := .seq (storageCall (.call copyPayload)) emitSaved

abbrev eraseDrop : Cmd 5 7 := .seq (storageCall (.call skipPayload)) (storageClear 6)

abbrev eraseBranch : Cmd 5 7 := .ite 4 eraseDrop eraseKeep

theorem eraseBranch_eval (regs : Fin 5 → Bool) (key query payload tail output : List Bool)
    (hflag : regs 4 = decide (key = query)) :
    ∃ n ≤ 4 * key.length + 13 * payload.length + 19, ∃ final,
      Eval eraseBranch n
        (eraseData regs (Encoding.frame payload ++ tail) query output key.reverse)
        (eraseData final tail query
          (if key = query then output else Encoding.frame key ++ Encoding.frame payload ++ output) []) := by
  by_cases hk : key = query
  · have hf : regs 4 = true := by simpa [hk] using hflag
    have hs := storageCall_eval
      (skipPayload_eval (recordState regs (Encoding.frame payload ++ tail) [] query.reverse [] [] output)
        payload tail rfl) key.reverse
    let rr := readRegs regs 0 1 (some false)
    have hs' : Eval (storageCall (.call skipPayload)) (5 * payload.length + 5)
        (eraseData regs (Encoding.frame payload ++ tail) query output key.reverse)
        (eraseData rr tail query output key.reverse) := by
      simpa [eraseData, afterSkip, recordState, rr, Nat.add_assoc] using hs
    have hc := storageClear_eval (eraseData rr tail query output key.reverse) 6
    let rr' := readRegs rr 0 1 none
    have hc' : Eval (storageClear 6) (2 * key.length + 3)
        (eraseData rr tail query output key.reverse) (eraseData rr' tail query output []) := by
      convert hc using 1
      · simp [eraseData, extendStorage]
      · apply congrArg₂ StructuredProgram.State.mk
        · rfl
        · funext i; fin_cases i <;>
            simp [eraseData, extendStorage, StackRoutines.clearStacks, storage]
    refine ⟨(5 * payload.length + 5) + (2 * key.length + 3) + 1, by omega, rr', ?_⟩
    simpa [eraseBranch, eraseDrop, hk] using (Eval.ite_true hf (hs'.seq hc') : Eval (.ite 4 eraseDrop eraseKeep) _ _ _)
  · have hf : regs 4 = false := by simpa [hk] using hflag
    have hs := storageCall_eval
      (copyPayload_eval (recordState regs (Encoding.frame payload ++ tail) [] query.reverse [] [] output)
        payload tail rfl rfl) key.reverse
    let rr := readRegs regs 0 1 none
    have hs' : Eval (storageCall (.call copyPayload)) (13 * payload.length + 12)
        (eraseData regs (Encoding.frame payload ++ tail) query output key.reverse)
        (eraseData rr tail query (Encoding.frame payload ++ output) key.reverse) := by
      simpa [eraseData, afterPayload, recordState, rr, Nat.add_assoc] using hs
    obtain ⟨final,he⟩ := emitSaved_eval rr tail query (Encoding.frame payload ++ output) key
    refine ⟨(13 * payload.length + 12) + (4 * key.length + 6) + 1, by omega, final, ?_⟩
    simpa [eraseBranch, eraseKeep, hk, List.append_assoc] using
      (Eval.ite_false hf (hs'.seq he) : Eval (.ite 4 eraseDrop eraseKeep) _ _ _)

abbrev eraseOne : Cmd 5 7 :=
  .seq (storageCall (.call (parseFrame 0 1)))
    (.seq (storageCopy 1 6 4) (.seq (storageCall compareDictionaryKey) eraseBranch))

theorem eraseOne_eval (regs : Fin 5 → Bool) (key query payload tail output : List Bool) :
    ∃ n ≤ 28 * key.length + 9 * query.length + 13 * payload.length + 50, ∃ final,
      Eval eraseOne n
        (eraseData regs (Encoding.frame key ++ Encoding.frame payload ++ tail) query output [])
        (eraseData final tail query
          (if key = query then output else Encoding.frame key ++ Encoding.frame payload ++ output) []) := by
  let source := Encoding.frame payload ++ tail
  let r0 := readRegs regs 0 1 (some false)
  have hp := storageCall_eval
    (parseFrame_eval (recordState regs (Encoding.frame key ++ source) [] query.reverse [] [] output)
      0 1 (by decide) key source rfl) []
  have hp' : Eval (storageCall (.call (parseFrame 0 1))) (6 * key.length + 5)
      (eraseData regs (Encoding.frame key ++ source) query output [])
      (extendStorage (recordState r0 source key.reverse query.reverse [] [] output) []) := by
    simpa [eraseData, afterFrame, recordState, r0, Nat.add_assoc] using hp
  let d := extendStorage (recordState r0 source key.reverse query.reverse [] [] output) []
  have hs := storageCopy_eval d 1 6 4 (by decide) (by decide) (by decide) (by simp [d,extendStorage,storage])
  let r1 := readRegs r0 0 1 none
  have hs' : Eval (storageCopy 1 6 4) (7 * key.length + 5) d
      (extendStorage (recordState r1 source key.reverse query.reverse [] [] output) key.reverse) := by
    convert hs using 1
    · simp [d,extendStorage,storage]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;>
          simp [d,extendStorage,storage,StackRoutines.copyStacks]
  obtain ⟨nc, hnc, r2, hc, hf⟩ := compareDictionaryKey_eval r1 source key query output
  have hc' := storageCall_eval hc key.reverse
  obtain ⟨nb, hnb, final,hb⟩ := eraseBranch_eval r2 key query payload tail output hf
  refine ⟨(6 * key.length + 5) + ((7 * key.length + 5) + ((nc + 1) + nb)), by omega, final, ?_⟩
  simpa only [eraseOne, source, List.append_assoc] using hp'.seq (hs'.seq (hc'.seq hb))
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
