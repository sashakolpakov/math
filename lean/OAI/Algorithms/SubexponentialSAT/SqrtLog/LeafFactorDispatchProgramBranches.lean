import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgramTest

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def mark (isHash isMarked : Bool) : Code :=
  .seq (.base (.atom (.set 5 isHash))) (.base (.atom (.set 6 isMarked)))
def marked (d : Data) (isHash isMarked : Bool) : Data :=
  ⟨Function.update (Function.update d.regs 5 isHash) 6 isMarked,d.stacks⟩

theorem mark_eval (d : Data) (isHash isMarked : Bool) :
    Eval (mark isHash isMarked) 2 d (marked d isHash isMarked) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (5 : Fin 8) isHash) d)).seq
    (Eval.base (StructuredProgram.Eval.atom (.set (6 : Fin 8) isMarked) _))
  simpa [mark,marked,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h

def hashBranch : Code := .seq (fetch false) (mark true false)
def neutralBranch : Code := .seq (clear 6) (mark false false)
def markedBranch : Code := .seq (clear 6)
  (.seq (copy 4 6) (.seq (fetch true) (mark false true)))

def finishedStacks (d : Data) (bits : List Bool) : Fin 16 → List Bool :=
  Function.update (Function.update d.stacks 6 []) 15 bits

def Finished (d e : Data) (isHash isMarked : Bool) (bits : List Bool) : Prop :=
  e.stacks=finishedStacks d bits ∧ e.regs 5=isHash ∧ e.regs 6=isMarked ∧ e.regs 7=d.regs 7

def FetchClean (d : Data) : Prop :=
  ∀ j ∈ ([10,11,12,15] : List (Fin 16)), d.stacks j=[]

theorem hashBranch_eval (d : Data) (rows : List (List Bool)) (i : Fin rows.length)
    (hm : d.stacks 0=Encoding.encodeList id rows) (hi : d.stacks 6=Encoding.encodeNat i.val)
    (hc : FetchClean d) :
    ∃ n e, n ≤ 23*(Encoding.encodeList id rows).length+21 ∧ Eval hashBranch n d e ∧
      Finished d e true false rows[i.val] := by
  obtain ⟨flag,n,hn,he⟩ := fetch_eval false d rows i hm hi hc
  refine ⟨n+2,marked (fetched d flag rows[i.val]) true false,by omega,
    he.seq (mark_eval _ true false),?_⟩
  simp [Finished,finishedStacks,marked,fetched]

theorem neutralBranch_eval (d : Data) (f : ℕ)
    (hi : d.stacks 6=Encoding.encodeNat f) (hout : d.stacks 15=[]) :
    ∃ e, Eval neutralBranch (2*f+7) d e ∧ Finished d e false false [] := by
  refine ⟨marked (cleared d 6) false false,?_,?_⟩
  · simpa [neutralBranch,hi,Nat.mul_add,Nat.add_assoc] using
      (clear_eval d 6).seq (mark_eval (cleared d 6) false false)
  · simp [Finished,finishedStacks,marked,cleared,hout,readRegs]

theorem markedBranch_eval (d : Data) (clauses : List (List Bool)) (i : Fin clauses.length) (f : ℕ)
    (hm : d.stacks 1=Encoding.encodeList id clauses) (hi : d.stacks 6=Encoding.encodeNat f)
    (hmark : d.stacks 4=Encoding.encodeNat i.val) (hc : FetchClean d) (htmp : d.stacks 14=[]) :
    ∃ n e, n ≤ 2*f+7*i.val+23*(Encoding.encodeList id clauses).length+38 ∧
      Eval markedBranch n d e ∧ Finished d e false true clauses[i.val] := by
  let a := cleared d 6
  let b := afterCopy a 4 6 0 1
  have h1 : Eval (clear 6) (2*f+5) d a := by
    simpa [a,hi,Nat.mul_add,Nat.add_assoc] using clear_eval d 6
  have h2 : Eval (copy 4 6) (7*(i.val+1)+5) a b := by
    simpa [copy,b,a,afterCopy,StackRoutines.copyStacks,cleared,hmark] using copy_eval a 4 6 14 0 1
      (by decide) (by decide) (by decide) (by decide) (by simpa [a,cleared] using htmp)
  have hbClean : FetchClean b := by
    intro j hj
    have h6 : j≠6 := by intro h; subst j; simp at hj
    simpa [b,a,afterCopy,StackRoutines.copyStacks,cleared,h6] using hc j hj
  obtain ⟨flag,n,hn,he⟩ := fetch_eval true b clauses i
    (by simpa [b,a,afterCopy,StackRoutines.copyStacks,cleared,masterPort] using hm)
    (by simp [b,a,afterCopy,StackRoutines.copyStacks,cleared,hmark]) hbClean
  let e := marked (fetched b flag clauses[i.val]) false true
  refine ⟨2*f+5+(7*(i.val+1)+5+(n+2)),e,by omega,
    h1.seq (h2.seq (he.seq (mark_eval _ false true))),?_⟩
  refine ⟨?_,by simp [e,marked],by simp [e,marked],?_⟩
  · funext j
    fin_cases j <;> simp [e,marked,fetched,b,a,afterCopy,StackRoutines.copyStacks,cleared,finishedStacks]
  · simp [e,marked,fetched,b,a,afterCopy,cleared,readRegs]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
