import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

/-! Runtime scatter of head bits into the original ambient coordinate order.
Coordinate identifiers are framed unary words; array replacement is a genuine
runtime scan. No coordinate permutation is compiled into the instruction table. -/
namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

open SubexponentialSAT BitProgram StructuredCalls Subexp.MatrixProgramSupport

abbrev Data := State 8 13
abbrev Code := Cmd 8 13
abbrev unary (n : ℕ) := List.replicate n true

def indices (js : List ℕ) : List Bool := ProgramEncoding.encodeRecords (js.map unary)

/-- The three persistent input stacks are 10, 11, 12. Working stacks are the
ambient mask 0, remaining bits 1, remaining identifiers 2, unary identifier 3,
replacement bit 4, constant width 5, and four array-scan workspaces 6--9. -/
def state (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool) : Data :=
  ⟨regs, ![mask,bits,indices js,[],[],[true],[],[],[],[],saved 0,saved 1,saved 2]⟩

def arrayPorts : Fin 8 → Fin 13 := ![0,4,3,5,6,7,8,9]

theorem arrayPorts_injective : Function.Injective arrayPorts := by decide

def replaceBit : Code := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.replaceProgram (0 : Fin 8) 1)
    id arrayPorts)

def popBit : Code := .base (.atom (.pop 1 0 1))
def pushBit : Code := .base (.atom (.push 4 0))
def clearBit : Code := .call (StackRoutines.clearProgram 4 (0 : Fin 8) 1)

def popIndexTag : Code := .base (.atom (.pop 2 0 1))

def scatterStep : Code :=
  .seq popIndexTag (.seq (readFrame 2 3 (by decide))
    (.seq popBit (.seq pushBit (.seq replaceBit clearBit))))

def write (mask : List Bool) (j : ℕ) (bit : Bool) : List Bool :=
  mask.take j ++ bit :: mask.drop (j+1)

theorem write_length (mask : List Bool) (j : ℕ) (bit : Bool) (hj : j < mask.length) :
    (write mask j bit).length = mask.length := by
  simp [write, List.length_take, List.length_drop, Nat.min_eq_left hj.le]
  omega

theorem scatterStep_eval (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (j : ℕ) (js : List ℕ) (bit : Bool) (bits mask : List Bool) (hj : j < mask.length) :
    ∃ rf, Eval scatterStep (30*j+53)
      (state regs saved (j::js) (bit::bits) mask)
      (state rf saved js bits (write mask j bit)) := by
  let d := state regs saved (j::js) (bit::bits) mask
  let d0 : Data := ⟨readRegs d.regs 0 1 (some true),
    Function.update d.stacks 2 (Encoding.frame (unary j) ++ indices js)⟩
  have htag : Eval popIndexTag 1 d d0 := by
    simpa [popIndexTag,d0,d,state,indices,ProgramEncoding.encodeRecords,Encoding.encodeList,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using
      (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.pop (2 : Fin 13) (0 : Fin 8) 1) d))
  obtain ⟨a, ha, hsa⟩ := readFrame_eval (2 : Fin 13) 3 (by decide) d0
    (unary j) (indices js) (by simp [d0]) (by simp [d0,d,state])
  let b : Data := ⟨readRegs a.regs 0 1 (some bit), Function.update a.stacks 1 bits⟩
  have hb : Eval popBit 1 a b := by
    have hs : a.stacks 1 = bit::bits := by rw [hsa]; rfl
    simpa [popBit,b,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hs] using
      (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.pop (1 : Fin 13) (0 : Fin 8) 1) a))
  let c : Data := ⟨b.regs, Function.update b.stacks 4 [bit]⟩
  have hc : Eval pushBit 1 b c := by
    have hs : a.stacks 4 = [] := by simp [hsa,d0,d,state]
    simpa [pushBit,c,b,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hs,readRegs] using
      (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.push (4 : Fin 13) (0 : Fin 8)) b))
  let earlier := (mask.take j).map (fun x => [x])
  have hearly : earlier.flatten = mask.take j := by
    change ((mask.take j).map (fun x => [x])).flatten = mask.take j
    induction mask.take j with
    | nil => rfl
    | cons x xs ih => simpa only [List.map_cons,List.flatten_cons,List.singleton_append] using congrArg (List.cons x) ih
  have helen : earlier.length = j := by
    simp [earlier,List.length_take,Nat.min_eq_left hj.le]
  have hsplit : mask = earlier.flatten ++ ([mask[j]] ++ mask.drop (j+1)) := by
    rw [hearly]
    have h := List.take_append_drop j mask
    rw [List.drop_eq_getElem_cons hj] at h
    simp
  let v := projectState id arrayPorts c
  have hrep := ArrayUpdatePrograms.replaceProgram_trace (0 : Fin 8) 1 (by decide)
    earlier [mask[j]] [bit] (mask.drop (j+1)) [true] (unary j) v.regs v.stacks
    (by simpa [v,projectState,arrayPorts,c,b,hsa,d0,d,state] using hsplit)
    (by simp [v,projectState,arrayPorts,c])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state,unary])
    (by simp [helen,unary])
    (by intro row hr; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr; rfl)
    rfl rfl
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
  let out : State 8 8 := ⟨readRegs v.regs 0 1 none,
    ArrayUpdatePrograms.replaceStacks earlier [bit] (mask.drop (j+1)) v.stacks⟩
  have hr := eval_call_from_state (ArrayUpdatePrograms.replaceProgram (0 : Fin 8) 1)
    id arrayPorts c Function.injective_id arrayPorts_injective (b := out) hrep
  let e : Data := ⟨readRegs c.regs 0 1 none,
    Function.update (Function.update c.stacks 0 (write mask j bit)) 3 []⟩
  have hout : embedState id arrayPorts c out = e := by
    apply embedState_eq_of_ports id arrayPorts c e out
      Function.injective_id arrayPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;>
        simp [e,out,v,projectState,arrayPorts,ArrayUpdatePrograms.replaceStacks,write,hearly]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [arrayPorts] using h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨2,by simpa [arrayPorts] using h.symm⟩
      simp [e,h0,h3]
  rw [hout] at hr
  have hclear := StackRoutines.clearProgram_trace (4 : Fin 13) (0 : Fin 8) 1 e.regs e.stacks
  have hh := StackRoutines.halt_after_trace _ hclear 2 rfl rfl
  let f : Data := ⟨readRegs e.regs 0 1 none, StackRoutines.clearStacks 4 e.stacks⟩
  have hf : Eval clearBit (2*(e.stacks 4).length+3) e f := by
    apply Eval.call
    simpa [clearBit,f,StackRoutines.clearResult,StructuredProgram.State.withPC,
      StackRoutines.clearProgram,Nat.add_assoc] using hh
  have hfinal : f = state f.regs saved js bits (write mask j bit) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i; fin_cases i <;> simp [e,c,b,hsa,d0,d,state,StackRoutines.clearStacks]
  rw [hfinal] at hf
  refine ⟨f.regs, ?_⟩
  have he := htag.seq (ha.seq (hb.seq (hc.seq (hr.seq hf))))
  convert he using 1 <;> simp [scatterStep,replaceBit,helen,unary,e,c] ; omega

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
