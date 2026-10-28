import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeMarked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeExport

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram

theorem workspace_eq_stacks (a b : Query.Data) (h : Marked.Wide.workspace a=Marked.Wide.workspace b)
    (i : Fin 768) (hi : i.val < 320 ∨ (324 : ℕ) < i.val) : a.stacks i=b.stacks i := by
  by_cases hlo : i.val < 320
  · let j : Fin 763 := ⟨i.val,by omega⟩
    have hj : Marked.Wide.workPort j=i := by simp [Marked.Wide.workPort,j,hlo]
    exact hj ▸ congrFun h j
  · let j : Fin 763 := ⟨i.val-5,by have := i.isLt; omega⟩
    have hj : Marked.Wide.workPort j=i := by
      apply Fin.ext
      have hjlo : ¬j.val < 320 := by dsimp [j]; omega
      simp [Marked.Wide.workPort,hjlo,j]
      omega
    exact hj ▸ congrFun h j

noncomputable def collect (k : ℕ) : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram (Marked.Wide.program (Query.marked k)) id workerStack)

theorem collect_eval (k : ℕ) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : FrameData) (records : List (List Bool))
    (hq : Marked.Wide.QueryValueContract (Query.marked k) count queryCost width
      (fun w => w=Marked.Wide.workspace (projectState id workerStack a)) valid)
    (hr : ∀ bits∈records, valid bits)
    (h320 : a.stacks 320=Encoding.encodeList id records) (h321 : a.stacks 321=[])
    (h323 : a.stacks 323=[]) (h324 : a.stacks 324=[]) :
    ∃ t b, t ≤ Marked.Wide.valueBudget queryCost width records (a.stacks 322) ∧
      Eval (collect k) t a b ∧
      BinaryArithmetic.toNat (b.stacks 322)=BinaryArithmetic.toNat (a.stacks 322)+(records.map count).sum ∧
      (b.stacks 322).length ≤ (a.stacks 322).length+Marked.Wide.outputGrowth width records ∧
      b.stacks 320=[] ∧ b.stacks 321=[] ∧ b.stacks 323=[] ∧ b.stacks 324=[] ∧
      (∀ i : Fin 896, i.val < 320 ∨ (324 : ℕ) < i.val → b.stacks i=a.stacks i) := by
  let d := projectState id workerStack a
  obtain ⟨next,hi,hv,hl,t,ht,he⟩ := Marked.Wide.value_program_run_length
    (Query.marked k) count queryCost width (fun w => w=Marked.Wide.workspace d) valid hq
    records [] d hr ⟨rfl,h323,h324⟩ (d.regs 16) (d.regs 17) (d.regs 18)
  have hstart : RecordPrograms.state Marked.Wide.recordPorts d
      (d.regs 16) (d.regs 17) (d.regs 18) (Encoding.encodeList id records++[]) []=d := by
    exact RecordPrograms.state_eq_self _ d _ _ _ _ _ rfl rfl rfl
      (by simpa [d,projectState,Marked.Wide.recordPorts,workerStack] using h320)
      (by simpa [d,projectState,Marked.Wide.recordPorts,workerStack] using h321)
  rw [hstart] at he
  let z := RecordPrograms.state Marked.Wide.recordPorts next false true false [] []
  let b := workerResult a z
  have hcall := eval_call_lifted (Marked.Wide.program (Query.marked k)) id workerStack a
    Function.injective_id (Fin.castAdd_injective 768 128) he
  have hrun : Eval (collect k) t a b := by
    simpa only [collect,b,workerResult,d,embedState_project id workerStack a
      Function.injective_id (Fin.castAdd_injective 768 128)] using hcall
  have hzwork : Marked.Wide.workspace z=Marked.Wide.workspace d :=
    (Marked.Wide.workspace_recordState _ _ _ _ _ _).trans hi.1
  have hlow (i : Fin 768) : b.stacks (workerStack i)=z.stacks i := workerResult_low a z i
  have hb322 : b.stacks 322=next.stacks 322 := by
    change b.stacks (workerStack (322 : Fin 768))=next.stacks 322
    simpa [z,RecordPrograms.state,Marked.Wide.recordPorts] using hlow 322
  refine ⟨t,b,ht,hrun,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hb322]; exact hv
  · rw [hb322]; exact hl
  · change b.stacks (workerStack (320 : Fin 768))=[]
    simpa [z,RecordPrograms.state,Marked.Wide.recordPorts] using hlow 320
  · change b.stacks (workerStack (321 : Fin 768))=[]
    simpa [z,RecordPrograms.state,Marked.Wide.recordPorts] using hlow 321
  · change b.stacks (workerStack (323 : Fin 768))=[]
    simpa [z,RecordPrograms.state,Marked.Wide.recordPorts,hi.2.1] using hlow 323
  · change b.stacks (workerStack (324 : Fin 768))=[]
    simpa [z,RecordPrograms.state,Marked.Wide.recordPorts,hi.2.2] using hlow 324
  · intro i hi
    by_cases hlo : i.val < 768
    · let j : Fin 768 := ⟨i.val,hlo⟩
      have hj : workerStack j=i := rfl
      rw [←hj,hlow j]
      exact workspace_eq_stacks z d hzwork j hi
    · exact workerResult_high a z i (by omega)

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
