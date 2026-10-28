import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScalarLiteralProgram
import OAI.Algorithms.SubexponentialSAT.SubexpTableSource
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyExecution
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Convert selected scalar coefficient words and raw Ce payloads into the
prepared literal rows consumed by the concrete table-source constructor. -/

namespace SubexponentialSAT.SubexpPreparedFactor

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

abbrev Coordinate := SubexpTableSource.Coordinate
abbrev Row := SubexpTableSource.Row
abbrev Data := State 5 22
abbrev Code := Cmd 5 22
abbrev Buffers := Fin 3 → Word

def prepareCoordinate (D : ℕ) (c : Coordinate) : Coordinate :=
  ⟨c.input, c.coefficients.map (SubexpScalarLiteralProgram.rawLiteral D)⟩

def prepareRow (D : ℕ) (r : Row) : Row :=
  ⟨SubexpScalarLiteralProgram.rawLiteral D r.value,
    r.coordinates.map (prepareCoordinate D)⟩

def prepareRows (D : ℕ) (rs : List Row) : List Row := rs.map (prepareRow D)

def bufferPort (i : Fin 3) : Fin 22 := ⟨15 + i.val, by omega⟩

def stores (D : ℕ) (input scalar : Word) (a : Buffers)
    (parser payload scratch : Word) : Fin 22 → Word := fun i =>
  if i = 0 then input else if i = 3 then scalar else
    if i = 7 then List.replicate D true else
    if i = 8 then List.replicate (SubexpSymbolicCost.indexBits D) true else
    if i = 15 then a 0 else if i = 16 then a 1 else if i = 17 then a 2 else
    if i = 18 then parser else if i = 19 then payload else if i = 20 then scratch else []

def work (regs : Fin 5 → Bool) (D : ℕ) (input scalar : Word) (a : Buffers)
    (parser payload scratch : Word) : Data :=
  ⟨regs, stores D input scalar a parser payload scratch⟩

def ready (regs : Fin 5 → Bool) (D : ℕ) (input : Word) (a : Buffers) : Data :=
  work regs D input [] a [] [] []

def emit (i : Fin 3) (bits : Word) (a : Buffers) : Buffers :=
  Function.update a i (bits.reverse ++ a i)

def record (bits : Word) : Word := true :: Encoding.frame bits

def atom (a : StructuredProgram.Atom 5 22) : Code := .base (.atom a)
local infixr:60 " ;; " => Cmd.seq

def pushBit (dst : Fin 22) (b : Bool) : Code := atom (.set 0 b) ;; atom (.push dst 0)
def clear (src : Fin 22) : Code := .call (StackRoutines.clearProgram src 0 1)
def transfer (src dst : Fin 22) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def popTag : Code := atom (.pop 0 0 1)

def parserRegs : Fin 2 → Fin 5 := Fin.castAdd 3
def parserPorts : Fin 2 → Fin 22 := ![0, 18]
def capturePorts (dst : Fin 22) : Fin 3 → Fin 22 := ![0, 18, dst]
def smallRegs : Fin 3 → Fin 5 := Fin.castAdd 2
def scalarPorts : Fin 15 → Fin 22 := Fin.castAdd 7

def captureBody := { ExecCNFRecords.captureProgram with entry := 4 }

def unframe : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.unframeProgram parserRegs parserPorts)

def captureFrame (dst : Fin 22) : Code :=
  .call (ProgramLinking.liftProgram captureBody parserRegs (capturePorts dst))

def scalar : Code :=
  .call (ProgramLinking.liftProgram SubexpScalarLiteralProgram.program id scalarPorts)

def appendFrame (src dst : Fin 22) : Code :=
  liftCommand (SubexpBlockAssembly.appendFrame src dst) 0 0 smallRegs id

def appendRecord (src dst : Fin 22) : Code :=
  pushBit dst true ;; appendFrame src dst

/-- The literal service constructs the zero exponent key and singleton raw
polynomial; the surrounding calls frame its actual output bytes. -/
def emitScalar (dst : Fin 22) (tag : Bool) : Code :=
  pushBit 3 false ;; scalar ;;
    (if tag then appendRecord 3 dst else appendFrame 3 dst) ;; clear 3

def scanBare (body : Code) : Code := popTag ;; .while 0 (body ;; popTag)
def scan (body : Code) : Code := scanBare (unframe ;; body)

def closeInto (src dst : Fin 22) : Code :=
  pushBit src false ;; transfer src 19 ;; appendRecord 19 dst ;; clear 19

def coordinateBody : Code :=
  captureFrame 15 ;; scanBare (emitScalar 15 true) ;; closeInto 15 16

def rowBody : Code :=
  emitScalar 16 false ;; scan coordinateBody ;; closeInto 16 17

def reset : Code := atom (.set 0 false) ;; atom (.set 1 false) ;;
  atom (.set 2 false) ;; atom (.set 3 false) ;; atom (.set 4 false)

def command : Code := scan rowBody ;; pushBit 17 false ;; transfer 17 0 ;; reset
def program := compiled command 0 0

def emptyBuffers : Buffers := fun _ => []
def serviceState (D : ℕ) (input : Word) : Data := ready (fun _ => false) D input emptyBuffers

def afterPush (dst : Fin 22) (b : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 b, Function.update d.stacks dst (b :: d.stacks dst)⟩

theorem pushBit_eval (dst : Fin 22) (b : Bool) (d : Data) :
    Eval (pushBit dst b) 2 d (afterPush dst b d) := by
  have h := Eval.seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 b) d))
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push dst 0)
      ((StructuredProgram.Atom.set (s := 22) 0 b).eval d)))
  simpa [pushBit, atom, afterPush, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def afterClear (src : Fin 22) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

theorem clear_eval (src : Fin 22) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (afterClear src d) :=
  Eval.call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

def afterTransfer (src dst : Fin 22) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 22) (hne : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer src dst d) :=
  Eval.call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

def frameRegs (r : Fin 5 → Bool) : Fin 5 → Bool :=
  Function.update (Function.update (Function.update r 0 false) 1 false) 2 true

def afterFrame (dst : Fin 22) (payload : Word) (d : Data) : Data :=
  ⟨frameRegs d.regs, Function.update d.stacks dst ((Encoding.frame payload).reverse ++ d.stacks dst)⟩

theorem appendFrame_eval (src dst : Fin 22) (hsd : src ≠ dst)
    (hs : src ≠ 20) (hd : dst ≠ 20) (d : Data) (htmp : d.stacks 20 = []) :
    Eval (appendFrame src dst) (8 * (d.stacks src).length + 8)
      d (afterFrame dst (d.stacks src) d) := by
  let small := projectState smallRegs id d
  have he := SubexpBlockAssembly.appendFrame_eval src dst hsd hs hd small htmp
  have hr : Function.Injective smallRegs := Fin.castAdd_injective _ _
  have h := eval_liftCommand_from_state (SubexpBlockAssembly.appendFrame src dst) 0 0
    smallRegs id d hr Function.injective_id he
  have hf : embedState smallRegs id d
      (SubexpBlockAssembly.afterFrame dst (d.stacks src) small) =
      afterFrame dst (d.stacks src) d := by
    apply embedState_eq_of_ports _ _ _ _ _ hr Function.injective_id
    · intro i; fin_cases i <;> simp [afterFrame, frameRegs, smallRegs,
        SubexpBlockAssembly.afterFrame, SubexpHornerProgram.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2,h.symm⟩
      simp only [afterFrame, frameRegs, Function.update_of_ne h0,
        Function.update_of_ne h1, Function.update_of_ne h2]
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
  have hs0 : small.stacks src = d.stacks src := rfl
  rw [hs0,hf] at h
  simpa only [appendFrame, Nat.add_assoc] using h

def afterRecord (dst : Fin 22) (payload : Word) (d : Data) : Data :=
  ⟨frameRegs d.regs, Function.update d.stacks dst ((record payload).reverse ++ d.stacks dst)⟩

theorem appendRecord_eval (src dst : Fin 22) (hsd : src ≠ dst)
    (hs : src ≠ 20) (hd : dst ≠ 20) (d : Data) (htmp : d.stacks 20 = []) :
    Eval (appendRecord src dst) (8 * (d.stacks src).length + 10)
      d (afterRecord dst (d.stacks src) d) := by
  have h1 := pushBit_eval dst true d
  have h2 := appendFrame_eval src dst hsd hs hd (afterPush dst true d)
    (by simp [afterPush,hd.symm,htmp])
  have hf : afterFrame dst ((afterPush dst true d).stacks src) (afterPush dst true d) =
      afterRecord dst (d.stacks src) d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      simp [frameRegs, afterPush]
    · funext i
      simp [afterPush, record, hsd, List.reverse_cons,
        List.append_assoc]
  have hlen : ((afterPush dst true d).stacks src).length = (d.stacks src).length := by
    simp [afterPush, hsd]
  rw [hlen, hf] at h2
  have h := h1.seq h2
  have hcost : 2 + (8 * (d.stacks src).length + 8) =
      8 * (d.stacks src).length + 10 := by
    omega
  rw [hcost] at h
  simpa only [appendRecord] using h

theorem reset_eval (d : Data) : Eval reset 5 d ⟨fun _ => false, d.stacks⟩ := by
  let a0 := StructuredProgram.Atom.set (s := 22) (0 : Fin 5) false
  let a1 := StructuredProgram.Atom.set (s := 22) (1 : Fin 5) false
  let a2 := StructuredProgram.Atom.set (s := 22) (2 : Fin 5) false
  let a3 := StructuredProgram.Atom.set (s := 22) (3 : Fin 5) false
  let a4 := StructuredProgram.Atom.set (s := 22) (4 : Fin 5) false
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom a0 d))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a1 (a0.eval d)))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a2 (a1.eval (a0.eval d))))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a3 (a2.eval (a1.eval (a0.eval d)))))
      (Eval.base (StructuredProgram.Eval.atom a4 (a3.eval (a2.eval (a1.eval (a0.eval d)))))))))
  have hf : a4.eval (a3.eval (a2.eval (a1.eval (a0.eval d)))) =
      (⟨fun _ => false, d.stacks⟩ : Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;>
        simp [a0,a1,a2,a3,a4,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    · rfl
  simpa only [reset, atom, hf] using h

end SubexponentialSAT.SubexpPreparedFactor

end OAI.Algorithms
