import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanForward
import OAI.Algorithms.SubexponentialSAT.SubexpPlanAlphabetEmit
import OAI.Algorithms.SubexponentialSAT.BankRoutines
import OAI.Algorithms.SubexponentialSAT.SubexpVertexIndexProgram

namespace OAI.Algorithms

/-!
# Fixed work bank for the all-vertex plan producer

The protected masters are the encoded scope list, D and Delta. A callback
copies them into the already checked per-vertex machine, emits a double-framed
plan record, and physically clears the work bank before the next vertex.
-/
namespace SubexponentialSAT.SubexpPlanAlphabetBase

open BitProgram StructuredCalls

abbrev Data := State 13 25
abbrev Code := Cmd 13 25
abbrev unary (n : ℕ) := List.replicate n true

def scopeBytes (scopes : List (List ℕ)) : List Bool :=
  Encoding.encodeList SubexpIncidencePlanScan.scopeBytes scopes

def regMap : Fin 10 → Fin 13 := Fin.castAdd 3
def stackMap : Fin 16 → Fin 25 := Fin.castAdd 9

theorem regMap_injective : Function.Injective regMap := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)
theorem stackMap_injective : Function.Injective stackMap := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 25 => x.val) h)

def localState (d : Data) : State 10 16 := ⟨d.regs ∘ regMap,d.stacks ∘ stackMap⟩

theorem embed_localState (d : Data) :
    embedState regMap stackMap d (localState d) = d := by
  apply embedState_eq_of_ports _ _ _ _ _ regMap_injective stackMap_injective
  all_goals intros; rfl

/-- Masters: 16 scopes, 17 D, 18 Delta. The vertex stream is on 21,
its current payload on 23, and the plan alphabet accumulator on 24. -/
def data (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (current source output payload : List Bool) : Data :=
  ⟨regs, ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],
    scopeBytes scopes,unary D,unary Δ,[],current,source,[],payload,output]⟩

theorem data_stacks_eq (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (current source output payload : List Bool) (i : Fin 25) :
    (data regs D Δ scopes current source output payload).stacks i =
      if i = 16 then scopeBytes scopes else if i = 17 then unary D
      else if i = 18 then unary Δ else if i = 20 then current
      else if i = 21 then source else if i = 23 then payload
      else if i = 24 then output else [] := by
  fin_cases i <;> rfl

def copied (src dst : Fin 25) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.copyStacks src dst d.stacks⟩
def copy (src dst : Fin 25) : Code :=
  .call (StackRoutines.copyProgram src dst 22 0 1)

theorem copy_eval (src dst : Fin 25) (hsd : src ≠ dst)
    (hst : src ≠ 22) (htd : (22 : Fin 25) ≠ dst) (d : Data)
    (ht : d.stacks 22 = []) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  Subexp.TupleProgram.copy_eval src dst 22 0 1 hsd hst htd (by decide) d ht

def prepare : Code := .seq (copy 16 6) (.seq (copy 17 10)
  (.seq (copy 18 11) (.seq (copy 23 2) (Subexp.TupleProgram.pushConst 2 0 false))))

def prepared (d : Data) : Data :=
  Subexp.TupleProgram.pushedState 2 0 false
    (copied 23 2 (copied 18 11 (copied 17 10 (copied 16 6 d))))

theorem prepare_eval (regs : Fin 13 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (current source output : List Bool) :
    Eval prepare (7*((scopeBytes scopes).length+D+Δ+v)+22)
      (data regs D Δ scopes current source output (unary v))
      (prepared (data regs D Δ scopes current source output (unary v))) := by
  let a := data regs D Δ scopes current source output (unary v)
  let b := copied 16 6 a
  let c := copied 17 10 b
  let d := copied 18 11 c
  let e := copied 23 2 d
  have h1 := copy_eval 16 6 (by decide) (by decide) (by decide) a rfl
  have h2 := copy_eval 17 10 (by decide) (by decide) (by decide) b rfl
  have h3 := copy_eval 18 11 (by decide) (by decide) (by decide) c rfl
  have h4' := copy_eval 23 2 (by decide) (by decide) (by decide) d rfl
  have h5 := Subexp.TupleProgram.pushConst_eval 2 0 false e
  have h := h1.seq (h2.seq (h3.seq (h4'.seq h5)))
  have hcost : (7*(a.stacks 16).length+5)+((7*(b.stacks 17).length+5)+
      ((7*(c.stacks 18).length+5)+((7*(d.stacks 23).length+5)+2))) =
      7*((scopeBytes scopes).length+D+Δ+v)+22 := by
    simp [a,b,c,d,data,copied,StackRoutines.copyStacks]
    ring
  rw [hcost] at h
  exact h

theorem prepared_local (regs : Fin 13 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (current source output : List Bool) :
    localState (prepared (data regs D Δ scopes current source output (unary v))) =
      SubexpIncidencePlanProgram.input
        ((prepared (data regs D Δ scopes current source output (unary v))).regs ∘ regMap)
        D Δ v scopes := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  fin_cases i <;>
    simp [prepared,data,copied,StackRoutines.copyStacks,scopeBytes,
      Subexp.TupleProgram.pushedState,stackMap,SubexpIncidencePlanScan.data,Encoding.encodeNat]

def runPlan : Code := .call
  (ProgramLinking.liftProgram SubexpIncidencePlanForward.program regMap stackMap)

theorem runPlan_eval (d : Data) (D Δ v : ℕ) (scopes : List (List ℕ))
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ)
    (hlocal : localState d = SubexpIncidencePlanProgram.input (d.regs ∘ regMap) D Δ v scopes) :
    ∃ n rf, Eval runPlan n d
      (embedState regMap stackMap d (SubexpIncidencePlanForward.finalState rf D Δ v scopes)) ∧
      n ≤ SubexpIncidencePlanProgram.bound D Δ v scopes + 3 +
        10*(ProgramEncoding.encodeRecords (Subexp.ReadPlan.unaryPlan
          (Subexp.IncidencePlanSpec.producedPlan D Δ scopes v))).length := by
  obtain ⟨n,rf,he,hn⟩ := SubexpIncidencePlanForward.command_eval_exact (d.regs ∘ regMap)
    D Δ v scopes hd
  have ht := eval_call_lifted SubexpIncidencePlanForward.program regMap stackMap d
    regMap_injective stackMap_injective (compiled_halt_trace he 6 0)
  rw [← hlocal,embed_localState] at ht
  exact ⟨n+1,rf,ht,by omega⟩

def emitRegs : Fin 3 → Fin 13 := ![0,1,2]
def emitStacks : Fin 3 → Fin 25 := ![0,3,24]
theorem emitRegs_injective : Function.Injective emitRegs := by decide
theorem emitStacks_injective : Function.Injective emitStacks := by decide

def emit : Code := .call
  (ProgramLinking.liftProgram SubexpPlanAlphabetEmit.program emitRegs emitStacks)

def emitted (d : Data) (rf : Fin 3 → Bool) (bits : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 (rf 0)) 1 (rf 1)) 2 (rf 2),
    Function.update (Function.update (Function.update d.stacks 0 []) 3 []) 24
      (true :: Encoding.frame (Encoding.frame bits) ++ d.stacks 24)⟩

theorem emit_eval (d : Data) (bits : List Bool) (h0 : d.stacks 0 = bits)
    (h3 : d.stacks 3 = []) :
    ∃ rf, Eval emit (24*bits.length+27) d (emitted d rf bits) := by
  obtain ⟨rf,ht⟩ := SubexpPlanAlphabetEmit.program_trace (d.regs ∘ emitRegs) bits (d.stacks 24)
  have ha : embedState emitRegs emitStacks d
      (SubexpPlanAlphabetEmit.data (d.regs ∘ emitRegs) bits [] (d.stacks 24)) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective emitStacks_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [emitStacks,SubexpPlanAlphabetEmit.data,h0,h3]
    · intros; rfl
  have hb : embedState emitRegs emitStacks d
      (SubexpPlanAlphabetEmit.data rf [] []
        (true :: Encoding.frame (Encoding.frame bits) ++ d.stacks 24)) = emitted d rf bits := by
    apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective emitStacks_injective
    · intro i; fin_cases i <;> simp [emitted,emitRegs,SubexpPlanAlphabetEmit.data]
    · intro i hi
      have h0' : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1' : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      have h2' : i ≠ 2 := fun h => hi ⟨2,h.symm⟩
      simp [emitted,h0',h1',h2']
    · intro i; fin_cases i <;> simp [emitted,emitStacks,SubexpPlanAlphabetEmit.data]
    · intro i hi
      have h0' : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h3' : i ≠ 3 := fun h => hi ⟨1,h.symm⟩
      have h24' : i ≠ 24 := fun h => hi ⟨2,h.symm⟩
      simp [emitted,h0',h3',h24']
  have h := eval_call_lifted SubexpPlanAlphabetEmit.program emitRegs emitStacks d
    emitRegs_injective emitStacks_injective ht
  rw [ha,hb] at h
  exact ⟨rf,h⟩

def clearPorts : List (Fin 25) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,23]
theorem clearPorts_nodup : clearPorts.Nodup := by decide

def cleanup : Code := BankRoutines.clearCmd 22 0 1 clearPorts

def cleaned (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,BankRoutines.clearBankStacks clearPorts d.stacks⟩

theorem cleanup_eval (d : Data) (h22 : d.stacks 22 = []) :
    Eval cleanup (2*(clearPorts.map (fun j => (d.stacks j).length)).sum+54) d (cleaned d) := by
  simpa [cleanup, cleaned, clearPorts] using
    BankRoutines.clear_eval 22 0 1 clearPorts clearPorts_nodup d.regs d.stacks h22

def callback : Code := .seq prepare (.seq runPlan (.seq emit cleanup))

end SubexponentialSAT.SubexpPlanAlphabetBase

/-! A closed callback for producing one framed forward vertex plan. -/
namespace SubexponentialSAT.SubexpPlanAlphabetBase

open BitProgram StructuredCalls

def planBytes (D Δ : ℕ) (scopes : List (List ℕ)) (v : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords
    (Subexp.ReadPlan.unaryPlan (Subexp.IncidencePlanSpec.vertexPlan D Δ scopes v))

def runStacks (D Δ v : ℕ) (scopes : List (List ℕ))
    (current source output : List Bool) : Fin 25 → List Bool :=
  ![planBytes D Δ scopes v,unary (scopes.length+D+v*Δ+Δ),(Encoding.encodeNat v).reverse,
    [],[],unary scopes.length,[],[],[],unary (Subexp.IncidencePlanSpec.degree scopes v),
    unary D,unary Δ,[],unary v,[],[],scopeBytes scopes,unary D,unary Δ,
    [],current,source,[],unary v,output]

theorem runStacks_eq (regs : Fin 13 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (current source output : List Bool) (rf : Fin 10 → Bool) (i : Fin 25) :
    runStacks D Δ v scopes current source output i =
      if hi : i.val < 16 then
        (SubexpIncidencePlanForward.finalState rf D Δ v scopes).stacks ⟨i.val,hi⟩
      else (prepared (data regs D Δ scopes current source output (unary v))).stacks i := by
  fin_cases i <;>
    simp [runStacks,SubexpIncidencePlanForward.finalState,
      SubexpIncidencePlanForward.result,SubexpIncidencePlanFinish.state,planBytes,
      Subexp.ReadPlan.unaryPlan,Subexp.IncidencePlanSpec.producedPlan,
      prepared,data,copied,StackRoutines.copyStacks,Subexp.TupleProgram.pushedState]

theorem runPlan_stacks (regs : Fin 13 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (current source output : List Bool) (rf : Fin 10 → Bool) :
    (embedState regMap stackMap
      (prepared (data regs D Δ scopes current source output (unary v)))
      (SubexpIncidencePlanForward.finalState rf D Δ v scopes)).stacks =
      runStacks D Δ v scopes current source output := by
  funext i
  rw [runStacks_eq regs D Δ v scopes current source output rf i]
  by_cases hi : i.val < 16
  · simp only [dite_eq_left hi]
    have he : stackMap ⟨i.val,hi⟩ = i := Fin.ext rfl
    simpa only [he] using embedState_stack regMap stackMap
      (prepared (data regs D Δ scopes current source output (unary v)))
      (SubexpIncidencePlanForward.finalState rf D Δ v scopes) stackMap_injective ⟨i.val,hi⟩
  · simp only [dite_eq_right hi]
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hlt := j.isLt
    simp only [stackMap,Fin.val_castAdd] at hv
    omega

def callbackBound (D Δ v : ℕ) (scopes : List (List ℕ)) : ℕ :=
  SubexpIncidencePlanProgram.bound D Δ v scopes +
    7*((scopeBytes scopes).length+D+Δ+v) +
    10*(ProgramEncoding.encodeRecords (Subexp.ReadPlan.unaryPlan
      (Subexp.IncidencePlanSpec.producedPlan D Δ scopes v))).length +
    24*(planBytes D Δ scopes v).length +
    2*(2*scopes.length+2*D+v*Δ+2*Δ+Subexp.IncidencePlanSpec.degree scopes v+3*v+1)+106

theorem callback_eval (regs : Fin 13 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (current source output : List Bool)
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    ∃ (n : ℕ) (rf : Fin 13 → Bool),
      Eval callback n (data regs D Δ scopes current source output (unary v))
        (data rf D Δ scopes current source
          (true :: Encoding.frame (Encoding.frame (planBytes D Δ scopes v)) ++ output) []) ∧
      rf 10 = regs 10 ∧ rf 11 = regs 11 ∧ rf 12 = regs 12 ∧
      n ≤ callbackBound D Δ v scopes := by
  let a := prepared (data regs D Δ scopes current source output (unary v))
  have hp := prepare_eval regs D Δ v scopes current source output
  obtain ⟨n,rp,hr,hn⟩ := runPlan_eval a D Δ v scopes hd
    (prepared_local regs D Δ v scopes current source output)
  let b := embedState regMap stackMap a (SubexpIncidencePlanForward.finalState rp D Δ v scopes)
  have hb : b.stacks = runStacks D Δ v scopes current source output :=
    runPlan_stacks regs D Δ v scopes current source output rp
  obtain ⟨re,he⟩ := emit_eval b (planBytes D Δ scopes v)
    (by rw [hb]; rfl) (by rw [hb]; rfl)
  let c := emitted b re (planBytes D Δ scopes v)
  have hc22 : c.stacks 22 = [] := by simp [c,emitted,hb,runStacks]
  have hc := cleanup_eval c hc22
  have hsum : (clearPorts.map (fun j => (c.stacks j).length)).sum =
      2*scopes.length+2*D+v*Δ+2*Δ+Subexp.IncidencePlanSpec.degree scopes v+3*v+1 := by
    simp [clearPorts,c,emitted,hb,runStacks,Encoding.length_encodeNat]
    omega
  rw [hsum] at hc
  have hfinish : cleaned c =
      data (cleaned c).regs D Δ scopes current source
        (true :: Encoding.frame (Encoding.frame (planBytes D Δ scopes v)) ++ output) [] := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    fin_cases i <;> simp [BankRoutines.clearBankStacks,clearPorts,c,emitted,hb,
      runStacks]
  have h := hp.seq (hr.seq (he.seq hc))
  rw [hfinish] at h
  refine ⟨_,(cleaned c).regs,h,?_,?_,?_,?_⟩
  · have hf := embedState_register_frame regMap stackMap a
      (SubexpIncidencePlanForward.finalState rp D Δ v scopes) 10 (by decide)
    simpa [cleaned,c,emitted,b,a,prepared,copied,Subexp.TupleProgram.pushedState,
      readRegs,data] using hf
  · have hf := embedState_register_frame regMap stackMap a
      (SubexpIncidencePlanForward.finalState rp D Δ v scopes) 11 (by decide)
    simpa [cleaned,c,emitted,b,a,prepared,copied,Subexp.TupleProgram.pushedState,
      readRegs,data] using hf
  · have hf := embedState_register_frame regMap stackMap a
      (SubexpIncidencePlanForward.finalState rp D Δ v scopes) 12 (by decide)
    simpa [cleaned,c,emitted,b,a,prepared,copied,Subexp.TupleProgram.pushedState,
      readRegs,data] using hf
  · dsimp [callbackBound]
    omega

end SubexponentialSAT.SubexpPlanAlphabetBase

/-! A physical record iterator invokes the closed plan-producing callback. -/
namespace SubexponentialSAT.SubexpPlanAlphabetBase

open BitProgram StructuredCalls

def ports : RecordPrograms.Ports 13 25 :=
  ⟨10,11,12,21,23,by decide,by decide,by decide,by decide⟩

def parserRegs (regs : Fin 13 → Bool) (v pr f : Bool) : Fin 13 → Bool :=
  Function.update (Function.update (Function.update regs 10 v) 11 pr) 12 f

theorem parser_state (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (current source output payload source' payload' : List Bool) (v pr f : Bool) :
    RecordPrograms.state ports (data regs D Δ scopes current source output payload)
      v pr f source' payload' =
      data (parserRegs regs v pr f) D Δ scopes current source' output payload' := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  fin_cases i <;> rfl

theorem parserRegs_self (regs : Fin 13 → Bool) (v pr f : Bool)
    (hv : regs 10 = v) (hp : regs 11 = pr) (hf : regs 12 = f) :
    parserRegs regs v pr f = regs := by
  funext i
  by_cases h10 : i = 10 <;> by_cases h11 : i = 11 <;> by_cases h12 : i = 12 <;>
    subst_vars <;> simp_all [parserRegs]

def Invariant (D Δ : ℕ) (scopes : List (List ℕ)) (current : List Bool) (d : Data) : Prop :=
  ∃ regs out, d = data regs D Δ scopes current [] out []

def mappedPlan (D Δ : ℕ) (scopes : List (List ℕ)) (bits : List Bool) : List Bool :=
  Encoding.frame (planBytes D Δ scopes bits.length)

def effect (D Δ : ℕ) (scopes : List (List ℕ)) (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 24 = true :: (Encoding.frame (mappedPlan D Δ scopes bits) ++ a.stacks 24)

def Valid (Δ : ℕ) (scopes : List (List ℕ)) (bits : List Bool) : Prop :=
  ∃ v, bits = unary v ∧ Subexp.IncidencePlanSpec.degree scopes v ≤ Δ

def recordCost (D Δ : ℕ) (scopes : List (List ℕ)) (bits : List Bool) : ℕ :=
  callbackBound D Δ bits.length scopes

theorem callback_contract (D Δ : ℕ) (scopes : List (List ℕ)) (current : List Bool) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (recordCost D Δ scopes) (Invariant D Δ scopes current)
      (effect D Δ scopes) (Valid Δ scopes) := by
  intro bits tail base hbits hbase
  rcases hbits with ⟨v,rfl,hd⟩
  rcases hbase with ⟨regs,out,rfl⟩
  obtain ⟨n,rf,he,h10,h11,h12,hn⟩ := callback_eval
    (parserRegs regs false true false) D Δ v scopes current tail out hd
  have hf : parserRegs rf false true false = rf :=
    parserRegs_self rf false true false
      (by simpa [parserRegs] using h10) (by simpa [parserRegs] using h11)
      (by simpa [parserRegs] using h12)
  let nextOut := true :: Encoding.frame (Encoding.frame (planBytes D Δ scopes v)) ++ out
  refine ⟨n,data rf D Δ scopes current [] nextOut [],?_,⟨rf,nextOut,rfl⟩,?_,?_⟩
  · simpa [recordCost] using hn
  · simp [effect,mappedPlan,data,nextOut]
  · simpa only [parser_state,List.reverse_replicate,hf] using he

private theorem fold_emit (D Δ : ℕ) (scopes : List (List ℕ))
    (records accum : List (List Bool)) :
    records.foldl (fun out bits => true :: (Encoding.frame (mappedPlan D Δ scopes bits) ++ out))
      (ProgramEncoding.encodeRecords accum) =
      ProgramEncoding.encodeRecords (records.reverse.map (mappedPlan D Δ scopes) ++ accum) := by
  induction records generalizing accum with
  | nil => rfl
  | cons bits rest ih =>
      rw [List.foldl_cons]
      change rest.foldl _ (ProgramEncoding.encodeRecords (mappedPlan D Δ scopes bits :: accum)) = _
      rw [ih]
      simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
        List.append_assoc,List.singleton_append]

def scan : Code := RecordPrograms.iterate ports callback

theorem scan_eval (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (current : List Bool) (vertices : List ℕ) (accum : List (List Bool)) (suffix : List Bool)
    (hd : ∀ v ∈ vertices, Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    ∃ (n : ℕ) (rf : Fin 13 → Bool),
      Eval scan n
        (data regs D Δ scopes current
          (ProgramEncoding.encodeRecords (vertices.map unary) ++ suffix)
          (ProgramEncoding.encodeRecords accum) [])
        (data rf D Δ scopes current suffix
          (ProgramEncoding.encodeRecords
            (vertices.reverse.map (fun v => Encoding.frame (planBytes D Δ scopes v)) ++ accum)) []) ∧
      n ≤ 3 + RecordPrograms.budget (recordCost D Δ scopes) (vertices.map unary) := by
  let base := data regs D Δ scopes current [] (ProgramEncoding.encodeRecords accum) []
  obtain ⟨n,next,hn,hnext,history,he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (recordCost D Δ scopes)
    (Invariant D Δ scopes current) (effect D Δ scopes) (Valid Δ scopes)
    (callback_contract D Δ scopes current) (vertices.map unary) suffix base
    (by
      intro bits hb
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
      exact ⟨v,rfl,hd v hv⟩)
    ⟨regs,ProgramEncoding.encodeRecords accum,rfl⟩ (regs 10) (regs 11) (regs 12)
  have hout := history.fold_of_false (by simp) (fun d => d.stacks 24)
    (fun out bits => true :: (Encoding.frame (mappedPlan D Δ scopes bits) ++ out))
    (by intro bits a b h; exact h)
  rcases hnext with ⟨rf,out,rfl⟩
  have hout' : out = ProgramEncoding.encodeRecords
      (vertices.reverse.map (fun v => Encoding.frame (planBytes D Δ scopes v)) ++ accum) := by
    change out = (vertices.map unary).foldl
      (fun out bits => true :: (Encoding.frame (mappedPlan D Δ scopes bits) ++ out))
      (ProgramEncoding.encodeRecords accum) at hout
    rw [fold_emit] at hout
    simpa [List.map_reverse,List.map_map,mappedPlan,Function.comp_def] using hout
  rw [hout'] at he
  have hany : (vertices.map unary).any (fun _ => false) = false := by simp
  refine ⟨n,parserRegs rf false true false,?_,hn⟩
  simpa only [scan,base,parser_state,parserRegs_self regs (regs 10) (regs 11) (regs 12) rfl rfl rfl,
    hany,SubexpNormalizeProgram.unread_false] using he

end SubexponentialSAT.SubexpPlanAlphabetBase

/-!
# Actual all-vertices forward-plan alphabet

The machine generates the vertex indices itself from unary D, in descending
order. The checked callback prepends its output, so the final alphabet is in
ascending vertex order. Every alphabet payload is a framed forward read plan.
-/
namespace SubexponentialSAT.SubexpPlanAlphabetBase

open BitProgram StructuredCalls

def indexRegs : Fin 5 → Fin 13 := Fin.castAdd 8
def indexStacks : Fin 5 → Fin 25 := ![19,20,23,21,22]
theorem indexRegs_injective : Function.Injective indexRegs := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)
theorem indexStacks_injective : Function.Injective indexStacks := by decide

def indexCall : Code := .call
  (ProgramLinking.liftProgram SubexpVertexIndexProgram.program indexRegs indexStacks)
def makeIndices : Code := .seq (copy 17 19) indexCall

theorem makeIndices_eval (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ)) :
    ∃ rf, Eval makeIndices (6*D^2+17*D+10)
      (data regs D Δ scopes [] [] [] [])
      (data rf D Δ scopes (unary D)
        (ProgramEncoding.encodeRecords ((List.range' 0 D).reverse.map unary)) [] []) := by
  let a := data regs D Δ scopes [] [] [] []
  let b := copied 17 19 a
  let localData : State 5 5 := ⟨b.regs ∘ indexRegs,b.stacks ∘ indexStacks⟩
  have hc := copy_eval 17 19 (by decide) (by decide) (by decide) a rfl
  obtain ⟨next,ht,hn⟩ := SubexpVertexIndexProgram.program_trace D localData
    (by simp [localData,b,a,copied,StackRoutines.copyStacks,indexStacks,data]) rfl rfl rfl rfl
  let e := embedState indexRegs indexStacks b next
  have ha : embedState indexRegs indexStacks b localData = b := by
    apply embedState_eq_of_ports _ _ _ _ _ indexRegs_injective indexStacks_injective
    all_goals intros; rfl
  have he : e = data e.regs D Δ scopes (unary D)
      (ProgramEncoding.encodeRecords ((List.range' 0 D).reverse.map unary)) [] [] := by
    apply embedState_eq_of_ports _ _ _ _ _ indexRegs_injective indexStacks_injective
    · intro i
      exact embedState_register indexRegs indexStacks b next indexRegs_injective i
    · intro i hi
      exact embedState_register_frame indexRegs indexStacks b next i hi
    · rcases hn with ⟨h0,h1,h2,h3,h4⟩
      intro i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
      · exact h3.symm
      · exact h4.symm
    · intro i hi
      have h19 : i ≠ 19 := fun h => hi ⟨0,h.symm⟩
      have h20 : i ≠ 20 := fun h => hi ⟨1,h.symm⟩
      have h23 : i ≠ 23 := fun h => hi ⟨2,h.symm⟩
      have h21 : i ≠ 21 := fun h => hi ⟨3,h.symm⟩
      simp [b,a,copied,StackRoutines.copyStacks,data_stacks_eq,h19,h20,h21,h23]
  have h := eval_call_lifted SubexpVertexIndexProgram.program indexRegs indexStacks b
    indexRegs_injective indexStacks_injective ht
  rw [ha] at h
  change Eval indexCall _ b e at h
  rw [he] at h
  refine ⟨e.regs,?_⟩
  convert hc.seq h using 1
  · rfl
  · simp [a, data]
    ring

def initializeOutput : Code := Subexp.TupleProgram.pushConst 24 0 false

theorem initializeOutput_eval (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (current source : List Bool) :
    Eval initializeOutput 2 (data regs D Δ scopes current source [] [])
      (data (Function.update regs 0 false) D Δ scopes current source
        (ProgramEncoding.encodeRecords []) []) := by
  have h := Subexp.TupleProgram.pushConst_eval 24 0 false
    (data regs D Δ scopes current source [] [])
  convert h using 1
  · rfl
  · apply congrArg (StructuredProgram.State.mk _)
    funext i
    fin_cases i <;> rfl

def alphabet (D Δ : ℕ) (scopes : List (List ℕ)) : List (List Bool) :=
  (List.range' 0 D).map (fun v => Encoding.frame (planBytes D Δ scopes v))

@[simp] theorem alphabet_length (D Δ : ℕ) (scopes : List (List ℕ)) :
    (alphabet D Δ scopes).length = D := by
  simp [alphabet]

theorem alphabet_eq_finRange (D Δ : ℕ) (scopes : List (List ℕ)) :
    alphabet D Δ scopes = (List.finRange D).map
      (fun v => Encoding.frame (planBytes D Δ scopes v.val)) := by
  unfold alphabet
  rw [← List.range_eq_range',← List.map_coe_finRange,List.map_map]
  rfl

theorem alphabet_eq_readPlan (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    alphabet D Δ scopes = (List.finRange D).map (fun v =>
      Encoding.frame (ProgramEncoding.encodeRecords (Subexp.ReadPlan.unaryPlan
        (Subexp.ReadPlan.vertexPlan (Subexp.IncidencePlanSpec.pattern D scopes)
          (Subexp.IncidencePlanSpec.slots D Δ scopes hd) (List.finRange D)
          (List.finRange scopes.length) v)))) := by
  rw [alphabet_eq_finRange]
  apply List.map_congr_left
  intro v _
  unfold planBytes
  rw [Subexp.IncidencePlanSpec.vertexPlan_eq_readPlan D Δ scopes hd v]

def command : Code := .seq makeIndices (.seq initializeOutput scan)

def totalBound (D Δ : ℕ) (scopes : List (List ℕ)) : ℕ :=
  6*D^2+17*D+15+
    RecordPrograms.budget (recordCost D Δ scopes) ((List.range' 0 D).reverse.map unary)

/-- No vertex list or slot assignment is an input. The only structural premise
is the degree bound on the runtime scope list. -/
theorem command_eval (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ n rf, Eval command n (data regs D Δ scopes [] [] [] [])
      (data rf D Δ scopes (unary D) [] (ProgramEncoding.encodeRecords (alphabet D Δ scopes)) []) ∧
      n ≤ totalBound D Δ scopes := by
  obtain ⟨ri,hi⟩ := makeIndices_eval regs D Δ scopes
  have ho := initializeOutput_eval ri D Δ scopes (unary D)
    (ProgramEncoding.encodeRecords ((List.range' 0 D).reverse.map unary))
  have hv : ∀ v ∈ (List.range' 0 D).reverse,
      Subexp.IncidencePlanSpec.degree scopes v ≤ Δ := by
    intro v h
    obtain ⟨i,hi,hmem⟩ := List.mem_range'.mp (List.mem_reverse.mp h)
    exact hd ⟨v,by omega⟩
  obtain ⟨n,rf,hs,hn⟩ := scan_eval (Function.update ri 0 false) D Δ scopes (unary D)
    (List.range' 0 D).reverse [] [] hv
  simp only [List.append_nil,List.reverse_reverse] at hs
  exact ⟨_,rf,hi.seq (ho.seq hs),by dsimp [totalBound]; omega⟩

abbrev program : Program 13 25 (size command+1) := compiled command 16 24

theorem program_trace (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ n rf, n ≤ totalBound D Δ scopes+1 ∧
      Trace program n ((data regs D Δ scopes [] [] [] []).withPC (some program.entry))
        ((data rf D Δ scopes (unary D) [] (ProgramEncoding.encodeRecords (alphabet D Δ scopes)) []).withPC none) := by
  obtain ⟨n,rf,h,hn⟩ := command_eval regs D Δ scopes hd
  exact ⟨n+1,rf,by omega,compiled_halt_trace h 16 24⟩

theorem program_primitive (regs : Fin 13 → Bool) (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program*(totalBound D Δ scopes+1))
      (BitProgram.primitiveCfg program
        ((data regs D Δ scopes [] [] [] []).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((data rf D Δ scopes (unary D) []
          (ProgramEncoding.encodeRecords (alphabet D Δ scopes)) []).withPC none)) := by
  obtain ⟨n,rf,h,hn⟩ := command_eval regs D Δ scopes hd
  exact ⟨rf,(StructuredCalls.primitive_execution h 16 24).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1))⟩

end SubexponentialSAT.SubexpPlanAlphabetBase

end OAI.Algorithms
