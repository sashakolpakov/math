import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramNat

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def frameReadRegs : Fin 2 → Fin 8 := Fin.castAdd 6
def frameReadPorts {s : ℕ} (src dst : Fin s) : Fin 2 → Fin s := ParserProgram.pair src dst

theorem frameReadRegs_injective : Function.Injective frameReadRegs := Fin.castAdd_injective _ _
theorem frameReadPorts_injective {s : ℕ} (src dst : Fin s) (h : src ≠ dst) :
    Function.Injective (frameReadPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [frameReadPorts, ParserProgram.pair]

abbrev readFrame8 {s : ℕ} (src dst : Fin s) : Cmd 8 s :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram frameReadRegs (frameReadPorts src dst))

def afterFrame8 {s : ℕ} (d : State 8 s) (src dst : Fin s) (bits : List Bool) (rest : List Bool) : State 8 s :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst
      (bits.reverse ++ d.stacks dst)⟩

theorem readFrame8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst)
    (bits : List Bool) (rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (readFrame8 src dst) (6 * bits.length + 4) d (afterFrame8 d src dst bits rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : embedState frameReadRegs (frameReadPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
  have hb : embedState frameReadRegs (frameReadPorts src dst) d b = afterFrame8 d src dst bits rest := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadRegs, readRegs, b, ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [frameReadRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [frameReadRegs] using h.symm⟩
      simp [afterFrame8, readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [frameReadPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [frameReadPorts] using h.symm⟩
      simp [afterFrame8, hsrc, hdst]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.frameProgram frameReadRegs
    (frameReadPorts src dst) d frameReadRegs_injective (frameReadPorts_injective src dst hsd) ht
  simpa only [ha,hb,readFrame8] using h

abbrev transfer8 {s : ℕ} (src dst : Fin s) : Cmd 8 s :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 8) 1)

def afterTransfer8 {s : ℕ} (d : State 8 s) (src dst : Fin s) : State 8 s :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst) :
    Eval (transfer8 src dst) (3*(d.stacks src).length+3) d (afterTransfer8 d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [afterTransfer8,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

abbrev takeDictionaryRecord : Cmd 8 28 :=
  .seq (readFrame8 27 16) (.seq (readFrame8 27 18) (transfer8 18 17))

def takeDictionaryRecordProgram := compiled takeDictionaryRecord 27 17

def readRecordResult (d : State 8 28) (key coeff tail : List Bool) : State 8 28 :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update d.stacks
      27 tail) 16 key.reverse) 18 []) 17 coeff⟩

theorem readRecord_result (d : State 8 28) (key coeff tail : List Bool)
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = []) (h18 : d.stacks 18 = []) :
    afterTransfer8 (afterFrame8 (afterFrame8 d 27 16 key (Encoding.frame coeff ++ tail))
      27 18 coeff tail) 18 17 = readRecordResult d key coeff tail := by
  apply congrArg₂ StructuredProgram.State.mk
  · simp [afterFrame8,StackRoutines.readRegs_reset]
  · funext i
    by_cases h27 : i = 27
    · subst i; simp [afterFrame8,StackRoutines.transferStacks]
    · by_cases h16i : i = 16
      · subst i; simp [afterFrame8,StackRoutines.transferStacks,h16]
      · by_cases h18i : i = 18
        · subst i; simp [afterFrame8,StackRoutines.transferStacks]
        · by_cases h17i : i = 17
          · subst i; simp [afterFrame8,StackRoutines.transferStacks,h17,h18]
          · simp [afterFrame8,StackRoutines.transferStacks,h27,h16i,h18i,h17i]

theorem takeDictionaryRecord_eval (d : State 8 28) (key coeff tail : List Bool)
    (hinput : d.stacks 27 = Encoding.frame key ++ Encoding.frame coeff ++ tail)
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = []) (h18 : d.stacks 18 = []) :
    Eval takeDictionaryRecord (6*key.length+9*coeff.length+11)
      d (readRecordResult d key coeff tail) := by
  have h1 := readFrame8_eval d 27 16 (by decide) key (Encoding.frame coeff ++ tail)
    (by simpa [List.append_assoc] using hinput)
  let a := afterFrame8 d 27 16 key (Encoding.frame coeff ++ tail)
  have h2 := readFrame8_eval a 27 18 (by decide) coeff tail (by simp [a,afterFrame8])
  let b := afterFrame8 a 27 18 coeff tail
  have h3 := transfer8_eval b 18 17 (by decide)
  have h3' : Eval (transfer8 18 17) (3*coeff.length+3) b (afterTransfer8 b 18 17) := by
    simpa [b,a,afterFrame8,h18] using h3
  have he := h1.seq (h2.seq h3')
  have ht : (6*key.length+4)+((6*coeff.length+4)+(3*coeff.length+3)) =
      6*key.length+9*coeff.length+11 := by omega
  rw [ht] at he
  simpa only [takeDictionaryRecord,b,a,readRecord_result d key coeff tail h16 h17 h18] using he

theorem takeDictionaryRecord_trace (d : State 8 28) (key coeff tail : List Bool)
    (hinput : d.stacks 27 = Encoding.frame key ++ Encoding.frame coeff ++ tail)
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = []) (h18 : d.stacks 18 = []) :
    Trace takeDictionaryRecordProgram (6*key.length+9*coeff.length+12)
      (d.withPC (some takeDictionaryRecordProgram.entry))
      ((readRecordResult d key coeff tail).withPC none) := by
  simpa [takeDictionaryRecordProgram,Nat.add_assoc] using
    compiled_halt_trace (takeDictionaryRecord_eval d key coeff tail hinput h16 h17 h18) 27 17

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
