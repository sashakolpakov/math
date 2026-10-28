import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgramMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramRead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramLess
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramCompare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramPrepend

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure Tape where
  input : List Bool := []
  target : List Bool := []
  key : List Bool := []
  coeff : List Bool := []
  work : List Bool := []
  newkey : List Bool := []
  tmp : List Bool := []
  tmp2 : List Bool := []
  output : List Bool := []
  framed : List Bool := []

def tapes (a : Tape) : Fin 10 → List Bool :=
  ![a.input,a.target,a.key,a.coeff,a.work,a.newkey,a.tmp,a.tmp2,a.output,a.framed]
def machine (r : Fin 5 → Bool) (a : Tape) : State 5 10 := ⟨r,tapes a⟩

def readRegsMap : Fin 2 → Fin 5 := Fin.castAdd 3
def readPorts (src dst : Fin 10) : Fin 2 → Fin 10 := ParserProgram.pair src dst

abbrev readFrame (src dst : Fin 10) : Cmd 5 10 := .call
  (ProgramLinking.liftProgram ParserProgram.frameProgram readRegsMap (readPorts src dst))

def afterFrame (d : State 5 10) (src dst : Fin 10) (bits rest : List Bool) : State 5 10 :=
  ⟨readRegs d.regs 0 1 (some false), Function.update (Function.update d.stacks src rest) dst
    (bits.reverse ++ d.stacks dst)⟩

theorem readFrame_eval (d : State 5 10) (src dst : Fin 10) (hsd : src ≠ dst)
    (bits rest : List Bool) (hi : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (readFrame src dst) (6*bits.length+4) d (afterFrame d src dst bits rest) := by
  have hr : Function.Injective readRegsMap := Fin.castAdd_injective _ _
  have hp : Function.Injective (readPorts src dst) := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [readPorts,ParserProgram.pair]
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits++rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse++d.stacks dst)⟩
  have ha : embedState readRegsMap (readPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ hr hp
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hi
      · rfl
    · intros; rfl
  have hb : embedState readRegsMap (readPorts src dst) d b = afterFrame d src dst bits rest := by
    apply embedState_eq_of_ports _ _ _ _ _ hr hp
    · intro i; fin_cases i <;> simp [afterFrame,readRegsMap,readRegs,b,ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0,by simpa [readRegsMap] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1,by simpa [readRegsMap] using h.symm⟩
      simp [afterFrame,readRegs,h0,h1]
    · intro i; fin_cases i <;> simp [afterFrame,readPorts,ParserProgram.pair,b,hsd]
    · intro j hj
      have hs : j ≠ src := fun h => hj ⟨0,by simpa [readPorts] using h.symm⟩
      have hd : j ≠ dst := fun h => hj ⟨1,by simpa [readPorts] using h.symm⟩
      simp [afterFrame,hs,hd]
  have ht : Trace ParserProgram.frameProgram (6*bits.length+4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.frameProgram readRegsMap (readPorts src dst) d hr hp ht
  simpa only [ha,hb,readFrame] using h

abbrev transfer (src dst : Fin 10) : Cmd 5 10 :=
  .call (StackRoutines.transferProgram src dst (0:Fin 5) 1)
abbrev clear (src : Fin 10) : Cmd 5 10 := Squarefree.Program.clearAt src

theorem transfer_machine (regs : Fin 5 → Bool) (a b : Tape) (src dst : Fin 10)
    (hsd : src ≠ dst) (hs : StackRoutines.transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3*(tapes a src).length+3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0:Fin 5) 1 hsd (by decide) regs (tapes a)
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [transfer,machine,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc,hs] using hh

theorem clear_machine (regs : Fin 5 → Bool) (a b : Tape) (src : Fin 10)
    (hs : Function.update (tapes a) src [] = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa [clear,machine,Squarefree.Program.clearedAt,hs] using
    Squarefree.Program.clearAt_eval (machine regs a) src

def smallRegs : Fin 3 → Fin 5 := Fin.castAdd 2
def maskPorts : Fin 3 → Fin 10 := ![4,2,5]
def emitPorts : Fin 3 → Fin 10 := ![5,3,9]
def comparePorts : Fin 6 → Fin 10 := ![0,2,1,6,7,8]

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem maskPorts_injective : Function.Injective maskPorts := by decide
theorem emitPorts_injective : Function.Injective emitPorts := by decide
theorem comparePorts_injective : Function.Injective comparePorts := by decide

abbrev scanMask : Cmd 5 10 := .call (ProgramLinking.liftProgram scanProgram smallRegs maskPorts)
abbrev emit : Cmd 5 10 := .call
  (ProgramLinking.liftProgram Squarefree.Program.prependRecordProgram smallRegs emitPorts)
abbrev compare : Cmd 5 10 :=
  liftCommand Squarefree.Program.compareDictionaryKey 0 5 id comparePorts

abbrev header : Cmd 5 10 :=
  .seq (Squarefree.Program.readNat 4 5) (.base (.atom (.push 5 0)))
abbrev rewriteKey : Cmd 5 10 := .seq (transfer 2 4) (.seq header (.seq header scanMask))
abbrev hit : Cmd 5 10 := .seq emit (transfer 9 8)
abbrev miss : Cmd 5 10 := .seq (clear 3) (clear 5)
abbrev record : Cmd 5 10 := .seq (readFrame 0 2) (.seq (readFrame 0 3)
  (.seq rewriteKey (.seq compare (.ite 4 hit miss))))
abbrev recordBody : Cmd 5 10 := .seq record (.base (.atom (.peek 0 0 3)))
abbrev records : Cmd 5 10 := .while 3 recordBody

abbrev project : Cmd 5 10 := .seq (readFrame 0 1)
  (.seq (.base (.atom (.peek 0 0 3))) (.seq records (transfer 8 9)))
def program := compiled project 0 9

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
