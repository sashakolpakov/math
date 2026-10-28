import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerInit
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramLabelLoop

namespace OAI.Algorithms

/-! Concrete relocation of the labeller, key deduplicator, and bucket table. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev regs8 : Fin 8 → Fin 10 := Fin.castAdd 2
abbrev labelPorts : Fin 22 → Fin 24 := Fin.castAdd 2

def labelCall : Code := .call (ProgramLinking.liftProgram Label.program regs8 labelPorts)
def dedupPorts : Fin 8 → Fin 24 := ![20,1,2,3,4,5,6,7]
theorem dedupPorts_injective : Function.Injective dedupPorts := by decide

def dedupCall : Code := .call (ProgramLinking.liftProgram keyDedupProgram id dedupPorts)
def groupPorts : Fin 15 → Fin 24 := ![1,2,3,4,5,21,19,20,6,7,8,9,10,11,12]
theorem groupPorts_injective : Function.Injective groupPorts := by decide

def groupCall : Code := .call (ProgramLinking.liftProgram groupProgram regs8 groupPorts)
def groupCommand : Code := .seq labelCall (.seq dedupCall (.seq groupCall
  (WorkspaceCleanupProgram.command 0 1 [15,19])))

def labelledRecords (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : List Record := Label.labelled W rows js n (assignments h)
def keys (records : List Record) : List (List Bool) := attainedKeys records.reverse

def labelInput (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) : Data :=
  enumerated regs W (SubexponentialSAT.Subexp.MatrixProgramSupport.words (rows.map SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (HeadScatterProgram.indices js) (HeadScatterProgram.unary n) h

def labelledState (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (records : List Record) (keyBits : List Bool) (output : List Bool := []) : Data :=
  state regs W (SubexponentialSAT.Subexp.MatrixProgramSupport.words (rows.map SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (HeadScatterProgram.indices js) (HeadScatterProgram.unary n) [false]
    (SubexponentialSAT.Subexp.BucketProgram.encodeRecords records.reverse) keyBits output [] []

theorem label_eval (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h : ℕ) (hrows : ∀ row∈rows,row.length=h)
    (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    ∃ t ≤ Label.cost W rows js n (assignments h)+2, ∃ rf,
      Eval labelCall t (labelInput regs W rows js n h)
        (labelledState rf W rows js n (labelledRecords W rows js n h)
          (ProgramEncoding.encodeRecords ((labelledRecords W rows js n h).map Prod.fst).reverse)) := by
  let d := labelInput regs W rows js n h
  have hd : projectState regs8 labelPorts d = Label.state (regs ∘ regs8) W rows js n
      (assignments h) [] [false] := by
    apply congrArg (StructuredProgram.State.mk (regs ∘ regs8))
    funext i; fin_cases i <;> simp [d,labelInput,enumerated,state,labelPorts]
  obtain ⟨rs,k,hk,ht⟩ := Label.program_runsIn (regs ∘ regs8) W rows js n
    (assignments h) [] [false]
    (by intro bits hb row hr; rw [assignment_width hb]; exact hrows row hr)
    (by intro bits hb; rw [assignment_width hb]; exact hlen) hjs
  rw [←hd] at ht
  have he := eval_call_from_state Label.program regs8 labelPorts d
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) ht
  let out := Label.state rs W rows js n []
    (Label.recordOutput W rows js n (assignments h) [])
    (Label.keyOutput W rows (assignments h) [false])
  let e := embedState regs8 labelPorts d out
  have hkey : Label.keyOutput W rows (assignments h) [false] =
      ProgramEncoding.encodeRecords (((assignments h).map (fun bits => Label.key W bits rows)).reverse) := by
    simpa only [ProgramEncoding.encodeRecords, Encoding.encodeList, List.append_nil] using
      Label.keyOutput_eq W rows (assignments h) []
  have hs : e = labelledState e.regs W rows js n (labelledRecords W rows js n h)
      (ProgramEncoding.encodeRecords ((labelledRecords W rows js n h).map Prod.fst).reverse) := by
    apply embedState_eq_of_ports regs8 labelPorts d _ out
      (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)
    · intro i; exact embedState_register regs8 labelPorts d out (Fin.castAdd_injective _ _) i
    · intro i hi; exact embedState_register_frame regs8 labelPorts d out i hi
    · intro i; fin_cases i <;>
        simp [labelledState,state,labelPorts,out,Label.state,Label.recordOutput_eq,
          hkey,labelledRecords,Label.labelled,List.map_map,Function.comp_def,
          ProgramEncoding.encodeRecords,Encoding.encodeList]
    · intro i hi
      fin_cases i <;> simp_all [Fin.exists_fin_succ,labelPorts,labelledState,state,d,labelInput,enumerated]
  change Eval labelCall k d e at he
  rw [hs] at he
  exact ⟨k,hk,e.regs,he⟩

def dedupCost (records : List Record) : ℕ :=
  120*((ProgramEncoding.encodeRecords (records.map Prod.fst).reverse).length+1)^2

theorem dedup_eval (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (records : List Record) :
    ∃ t ≤ dedupCost records, ∃ rf,
      Eval dedupCall t
        (labelledState regs W rows js n records
          (ProgramEncoding.encodeRecords (records.map Prod.fst).reverse))
        (labelledState rf W rows js n records (ProgramEncoding.encodeRecords (keys records))) := by
  let d := labelledState regs W rows js n records
    (ProgramEncoding.encodeRecords (records.map Prod.fst).reverse)
  let a := projectState id dedupPorts d
  have ha : SubexponentialSAT.ExecLiteralDedupProgram.Ready a := by
    simp [a,projectState,d,dedupPorts,labelledState,state,SubexponentialSAT.ExecLiteralDedupProgram.Ready,
      SubexponentialSAT.ExecLiteralDedupProgram.Clean]
  obtain ⟨b,hb,hout,k,hk,ht⟩ := keyDedup_runsIn records.reverse a
    (by simp [a,projectState,d,dedupPorts,labelledState,state,List.map_reverse]) ha
  have he := eval_call_from_state keyDedupProgram id dedupPorts d
    Function.injective_id dedupPorts_injective ht
  let e := embedState id dedupPorts d b
  have hs : e = labelledState b.regs W rows js n records (ProgramEncoding.encodeRecords (keys records)) := by
    rcases hb with ⟨⟨h3,h4,h5,h6,h7⟩,h1,h2⟩
    apply embedState_eq_of_ports id dedupPorts d _ b Function.injective_id dedupPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp_all [dedupPorts,labelledState,state,keys]
    · intro i hi; fin_cases i <;> simp_all [Fin.exists_fin_succ,dedupPorts,labelledState,state,d]
  change Eval dedupCall k d e at he
  rw [hs] at he
  exact ⟨k,by simpa [dedupCost,List.map_reverse] using hk,b.regs,he⟩

def tableOutput (records : List Record) : List Bool :=
  ProgramEncoding.encodeRecords (SubexponentialSAT.Subexp.PackingBucketTable.table records (keys records))

theorem group_eval (regs : Fin 10 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (records : List Record) :
    ∃ t ≤ SubexponentialSAT.Subexp.PackingBucketTable.budget records (keys records), ∃ rf,
      Eval groupCall t (labelledState regs W rows js n records (ProgramEncoding.encodeRecords (keys records)))
        (labelledState rf W rows js n records [] (tableOutput records)) := by
  let d := labelledState regs W rows js n records (ProgramEncoding.encodeRecords (keys records))
  have hd : projectState regs8 groupPorts d =
      SubexponentialSAT.Subexp.PackingBucketTable.inputState records (keys records) 0 [] (regs ∘ regs8) := by
    apply congrArg (StructuredProgram.State.mk (regs ∘ regs8))
    funext i; fin_cases i <;> simp [groupPorts,d,labelledState,state]
  obtain ⟨k,hk,rs,ht⟩ := SubexponentialSAT.Subexp.PackingBucketTable.program_trace records (keys records)
    0 (Nat.zero_le _) [] (regs ∘ regs8)
  rw [←hd] at ht
  have he := eval_call_from_state groupProgram regs8 groupPorts d
    (Fin.castAdd_injective _ _) groupPorts_injective ht
  let out := SubexponentialSAT.Subexp.PackingBucketTable.outputState records (keys records) 0 [] rs
  let e := embedState regs8 groupPorts d out
  have hmin : SubexponentialSAT.Subexp.PackingBucketTable.minimum records (keys records) 0=0 :=
    Nat.eq_zero_of_le_zero (SubexponentialSAT.Subexp.PackingBucketTable.minimum_le _ _ _)
  have hs : e=labelledState e.regs W rows js n records [] (tableOutput records) := by
    apply embedState_eq_of_ports regs8 groupPorts d _ out
      (Fin.castAdd_injective _ _) groupPorts_injective
    · intro i; exact embedState_register regs8 groupPorts d out (Fin.castAdd_injective _ _) i
    · intro i hi; exact embedState_register_frame regs8 groupPorts d out i hi
    · intro i; fin_cases i <;> simp [groupPorts,labelledState,state,out,tableOutput,hmin,
        SubexponentialSAT.Subexp.PackingBucketTable.outputState,SubexponentialSAT.Subexp.PackingBucketCalls.state]
    · intro i hi; fin_cases i <;> simp_all [Fin.exists_fin_succ,groupPorts,labelledState,state,d]
  change Eval groupCall k d e at he
  rw [hs] at he
  exact ⟨k,hk,e.regs,he⟩

end SubexponentialSAT.SqrtLog.BucketProgram.Controller

end OAI.Algorithms
