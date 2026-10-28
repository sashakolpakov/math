import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSignature
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramRun

namespace OAI.Algorithms

/-! Physical production of a labelled full ambient assignment. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport
namespace Label
abbrev Data := State 8 22
abbrev Code := Cmd 8 22

def state (regs : Fin 8 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (pending : List (List Bool)) (records keys : List Bool) : Data :=
  ⟨regs, ![W,[],[],[],[],[],[],[],[],[],[],[],[],[],[],
    ProgramEncoding.encodeRecords pending,words (rows.map words),
    HeadScatterProgram.indices js,HeadScatterProgram.unary n,records,keys,[]]⟩

def signaturePorts : Fin 15 → Fin 22 := Fin.castAdd 7
def signatureCall : Code := .call (ProgramLinking.liftProgram signatureProgram id signaturePorts)
def scatterPorts : Fin 13 → Fin 22 := ![21,1,2,3,4,5,6,7,8,9,17,12,18]
theorem scatterPorts_injective : Function.Injective scatterPorts := by decide

def scatterCall : Code := .call
  (ProgramLinking.liftProgram HeadScatterProgram.program id scatterPorts)
def popTag : Code := .base (.atom (.pop 15 0 1))
def keyTag : Code := .base (.seq (.atom (.set 0 true)) (.atom (.push 20 0)))

def step : Code :=
  .seq popTag (.seq (readWord 15 12 11 (by decide))
    (.seq (copy 16 13 11) (.seq signatureCall (.seq scatterCall
      (.seq (copy 14 2 11) (.seq (emitFrame 2 20 11 (by decide))
        (.seq keyTag (.seq (emitFrame 21 19 11 (by decide))
          (.seq (emitFrame 14 19 11 (by decide))
            (WorkspaceCleanupProgram.command 0 1 [12]))))))))))

def key (W bits : List Bool) (rows : List (List (List Bool))) := signatureValue W bits rows

def stepCost (W bits : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) : ℕ :=
  1+(9*bits.length+7)+(7*(words (rows.map words)).length+5)+
  (signatureCost W bits rows+2)+HeadScatterProgram.totalCost n js bits+
  (7*(key W bits rows).length+5)+(8*(key W bits rows).length+8)+2+
  (8*n+8)+(8*(key W bits rows).length+8)+(2*bits.length+3)

theorem step_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (js : List ℕ) (n : ℕ)
    (pending : List (List Bool)) (records keys : List Bool)
    (hrows : ∀ row∈rows,row.length=bits.length)
    (hlen : js.length=bits.length) (hjs : ∀ j∈js,j < n) :
    ∃ t ≤ stepCost W bits rows js n, ∃ rf,
      Eval step t (state regs W rows js n (bits::pending) records keys)
        (state rf W rows js n pending
          (Encoding.frame (key W bits rows)++Encoding.frame (HeadScatterProgram.mask n js bits)++records)
          (true::(Encoding.frame (key W bits rows)++keys))) := by
  let d := state regs W rows js n (bits::pending) records keys
  let a : Data := ⟨readRegs regs 0 1 (some true),Function.update d.stacks 15
    (Encoding.frame bits++ProgramEncoding.encodeRecords pending)⟩
  have hea : Eval popTag 1 d a := by
    simpa [popTag,a,d,state,ProgramEncoding.encodeRecords,Encoding.encodeList,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using
      (Eval.base (StructuredProgram.Eval.atom (.pop (15 : Fin 22) (0 : Fin 8) 1) d))
  obtain ⟨b,heb,hsb⟩ := readWord_eval (15 : Fin 22) 12 11
    (by decide) (by decide) (by decide) a bits (ProgramEncoding.encodeRecords pending)
    (by simp [a]) (by simp [a,d,state]) (by simp [a,d,state])
  obtain ⟨c,hec,hsc⟩ := copy_eval (16 : Fin 22) 13 11
    (by decide) (by decide) (by decide) b (by simp [hsb,a,d,state])
  have hcproj : projectState id signaturePorts c = signatureState c.regs W bits rows [] := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i; fin_cases i <;>
      simp [signaturePorts,hsc,hsb,a,d,state,StackRoutines.copyStacks]
  obtain ⟨ts,hts,rs,hes⟩ := signatureCommand_eval c.regs W bits rows [] hrows
  simp only [List.append_nil] at hes
  rw [←hcproj] at hes
  have hesig := eval_call_from_state signatureProgram id signaturePorts c
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hes 13 14)
  let e : Data := ⟨rs,Function.update (Function.update c.stacks 13 []) 14 (key W bits rows)⟩
  have hse : embedState id signaturePorts c (signatureState rs W bits [] (key W bits rows))=e := by
    apply embedState_eq_of_ports id signaturePorts c _ _ Function.injective_id (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;>
        simp [e,key,signaturePorts,signatureState,words,hsc,hsb,a,d,state,StackRoutines.copyStacks]
    · intro i hi
      have h13 : i≠13 := fun h => hi ⟨13,h.symm⟩
      have h14 : i≠14 := fun h => hi ⟨14,h.symm⟩
      simp [e,h13,h14]
  change Eval signatureCall (ts+1) c (embedState id signaturePorts c
    (signatureState rs W bits [] (key W bits rows))) at hesig
  rw [hse] at hesig
  have heproj : projectState id scatterPorts e = HeadScatterProgram.input e.regs js bits n := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i; fin_cases i <;>
      simp [scatterPorts,e,hsc,hsb,a,d,state,StackRoutines.copyStacks
        ]
  obtain ⟨rt,het⟩ := HeadScatterProgram.command_eval e.regs n js bits hlen hjs
  rw [←heproj] at het
  have hescatter := eval_call_from_state HeadScatterProgram.program id scatterPorts e
    Function.injective_id scatterPorts_injective (compiled_halt_trace het 10 0)
  let f : Data := ⟨rt,Function.update e.stacks 21 (HeadScatterProgram.mask n js bits)⟩
  have hsf : embedState id scatterPorts e (HeadScatterProgram.result rt js bits n)=f := by
    apply embedState_eq_of_ports id scatterPorts e _ _ Function.injective_id scatterPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;>
        simp [f,scatterPorts,HeadScatterProgram.result,e,hsc,hsb,a,d,state,StackRoutines.copyStacks]
    · intro i hi
      have h21 : i≠21 := fun h => hi ⟨0,h.symm⟩
      simp [f,h21]
  change Eval scatterCall (HeadScatterProgram.totalCost n js bits-1+1) e
    (embedState id scatterPorts e (HeadScatterProgram.result rt js bits n)) at hescatter
  rw [hsf] at hescatter
  obtain ⟨g,heg,hsg⟩ := copy_eval (14 : Fin 22) 2 11
    (by decide) (by decide) (by decide) f (by simp [f,e,hsc,hsb,a,d,state,StackRoutines.copyStacks])
  obtain ⟨h,heh,hsh⟩ := emitFrame_eval (2 : Fin 22) 20 11
    (by decide) (by decide) (by decide) g
    (by simp [hsg,f,e,hsc,hsb,a,d,state,StackRoutines.copyStacks])
  let k : Data := ⟨Function.update h.regs 0 true,Function.update h.stacks 20 (true::h.stacks 20)⟩
  have hek : Eval keyTag 2 h k := by
    have hx := (StructuredProgram.Eval.atom (.set (0 : Fin 8) true) h).seq
      (StructuredProgram.Eval.atom (.push (20 : Fin 22) 0) _)
    exact .base (by simpa [k,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using hx)
  obtain ⟨l,hel,hsl⟩ := emitFrame_eval (21 : Fin 22) 19 11
    (by decide) (by decide) (by decide) k
    (by simp [k,hsh,hsg,f,e,hsc,hsb,a,d,state,StackRoutines.copyStacks])
  obtain ⟨m,hem,hsm⟩ := emitFrame_eval (14 : Fin 22) 19 11
    (by decide) (by decide) (by decide) l
    (by simp [hsl,k,hsh,hsg,f,e,hsc,hsb,a,d,state,StackRoutines.copyStacks])
  let q := WorkspaceCleanupProgram.finish (0 : Fin 8) 1 ([12] : List (Fin 22)) m
  have heq := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
    ([12] : List (Fin 22)) (by decide) m
  have hq : q = state q.regs W rows js n pending
      (Encoding.frame (key W bits rows)++Encoding.frame (HeadScatterProgram.mask n js bits)++records)
      (true::(Encoding.frame (key W bits rows)++keys)) := by
    apply congrArg (StructuredProgram.State.mk q.regs)
    funext i; fin_cases i <;>
      simp [BankRoutines.clearBankStacks,hsm,hsl,k,hsh,hsg,f,e,hsc,hsb,a,d,state,StackRoutines.copyStacks,List.append_assoc]
  have hrun := hea.seq (heb.seq (hec.seq (hesig.seq (hescatter.seq
    (heg.seq (heh.seq (hek.seq (hel.seq (hem.seq heq)))))))))
  change Eval step _ d q at hrun
  rw [hq] at hrun
  refine ⟨_,?_,q.regs,hrun⟩
  have hp : 1 ≤ HeadScatterProgram.totalCost n js bits := by
    unfold HeadScatterProgram.totalCost; omega
  have hm := HeadScatterProgram.mask_length n js bits hjs
  simp only [Nat.sub_add_cancel hp]
  simp [WorkspaceCleanupProgram.cost,hsm,hsl,k,hsh,hsg,f,e,hsc,hsb,a,d,state,
    StackRoutines.copyStacks,hm,stepCost]
  omega

end Label
end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
