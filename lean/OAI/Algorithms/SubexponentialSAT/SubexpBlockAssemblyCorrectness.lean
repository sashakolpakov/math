import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyTraversal
import OAI.Algorithms.SubexponentialSAT.SubexpTableSourceExecution

namespace OAI.Algorithms

/-! Actual prepared-table calls inside the whole-block packer. -/

namespace SubexponentialSAT.SubexpBlockAssembly

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

def actualCommand : Code := command SubexpTableSource.program
def actualProgram := program SubexpTableSource.program

@[simp] theorem bufferPort_zero : bufferPort 0 = 13 := rfl
@[simp] theorem bufferPort_one : bufferPort 1 = 14 := rfl
@[simp] theorem bufferPort_two : bufferPort 2 = 15 := rfl
@[simp] theorem bufferPort_three : bufferPort 3 = 16 := rfl
@[simp] theorem bufferPort_four : bufferPort 4 = 17 := rfl
@[simp] theorem bufferPort_five : bufferPort 5 = 18 := rfl
@[simp] theorem bufferPort_six : bufferPort 6 = 21 := rfl

theorem table_work_eval (rows : List SubexpTableSource.Row) (rest zero one : Word) (a : Buffers) :
    Eval (.call (ProgramLinking.liftProgram SubexpTableSource.program id tablePorts))
      (SubexpTableSource.tableCost zero one rows +
        3 * (SubexpTableSource.tableCode zero one rows).length + 6)
      (work false false false rest zero one a (SubexpTableSource.encodeRows rows) [])
      (work false false false rest zero one a (SubexpTableSource.tableCode zero one rows) []) := by
  let d := work false false false rest zero one a (SubexpTableSource.encodeRows rows) []
  have ha : embedState id tablePorts d
      (SubexpTableSource.serviceState (SubexpTableSource.encodeRows rows) zero one) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id tablePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState id tablePorts d
      (SubexpTableSource.serviceState (SubexpTableSource.tableCode zero one rows) zero one) =
      work false false false rest zero one a (SubexpTableSource.tableCode zero one rows) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id tablePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h19 : i ≠ 19 := fun h => hi ⟨0,by simpa [tablePorts] using h.symm⟩
      fin_cases i <;> simp_all [work,d]
  have h := eval_call_lifted SubexpTableSource.program id tablePorts d
    Function.injective_id tablePorts_injective (SubexpTableSource.program_trace zero one rows)
  rw [ha,hb] at h
  exact h

theorem table_work (rows : List SubexpTableSource.Row) (rest zero one : Word) (a : Buffers) :
    Executes (.call (ProgramLinking.liftProgram SubexpTableSource.program id tablePorts))
      (work false false false rest zero one a (SubexpTableSource.encodeRows rows) [])
      (work false false false rest zero one a (SubexpTableSource.tableCode zero one rows) []) :=
  ⟨_,table_work_eval rows rest zero one a⟩

def factorUpdate (zero one : Word) (rows : List SubexpTableSource.Row) (a : Buffers) : Buffers :=
  Function.update (emit 0 (SubexpTableSource.tableCode zero one rows) a) 1 (true :: a 1)

theorem factorBody_work (rows : List SubexpTableSource.Row) (v p c : Bool)
    (rest zero one : Word) (a : Buffers) :
    Executes (factorBody SubexpTableSource.program)
      (state v p c (Encoding.frame (SubexpTableSource.encodeRows rows) ++ rest) zero one a)
      (state true false false rest zero one (factorUpdate zero one rows a)) := by
  have h1 := capture_work v p c (SubexpTableSource.encodeRows rows) rest zero one a
  have h2 := reset_work false false c rest zero one (SubexpTableSource.encodeRows rows) a
  have h3 := table_work rows rest zero one a
  have h4 := transferPayload_work 0 false false false rest zero one
    (SubexpTableSource.tableCode zero one rows) a
  have h5 := pushBuffer_work 1 true false false false rest zero one
    (emit 0 (SubexpTableSource.tableCode zero one rows) a)
  have h := executes_seq h1 (executes_seq h2 (executes_seq h3 (executes_seq h4 h5)))
  simpa only [factorBody, bufferPort_zero, bufferPort_one, factorUpdate, emit,
    Function.update_of_ne (by decide :
    (1 : Fin 7) ≠ 0)] using h

theorem productPorts_injective : Function.Injective productPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [productPorts]

def drainUpdate (a : Buffers) : Buffers :=
  emit 0 (SubexpKernelControl.operators true (a 1).length) (Function.update a 1 [])

theorem drainProducts_work_eval (v p : Bool) (rest zero one : Word) (a : Buffers) :
    Eval drainProducts (4 * (a 1).length + 3) (state v p true rest zero one a)
      (state false false true rest zero one (drainUpdate a)) := by
  let localAcc : SubexpKernelControl.Accumulator := ⟨a 0,a 1,[],[]⟩
  let d := state v p true rest zero one a
  have ha : embedState id productPorts d
      (SubexpKernelControl.state v p rest zero one localAcc) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id productPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState id productPorts d
      (SubexpKernelControl.state false false rest zero one
        (SubexpKernelControl.emit (SubexpKernelControl.operators true (a 1).length)
          (SubexpKernelControl.setCounter 0 [] localAcc))) =
      state false false true rest zero one (drainUpdate a) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id productPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;>
        simp [state,work,productPorts,drainUpdate,emit,localAcc,
          SubexpKernelControl.state,SubexpKernelControl.emit,SubexpKernelControl.setCounter]
    · intro i hi
      have h13 : i ≠ 13 := fun h => hi ⟨3,by simpa [productPorts] using h.symm⟩
      have h14 : i ≠ 14 := fun h => hi ⟨5,by simpa [productPorts] using h.symm⟩
      fin_cases i <;> simp_all [d,state,work,drainUpdate,emit]
  have hd := SubexpKernelControl.drain_eval 0 true (a 1) v p rest zero one localAcc
  have hd' : Eval (SubexpKernelControl.drain 5 true) (4 * (a 1).length + 2)
      (SubexpKernelControl.state v p rest zero one localAcc)
      (SubexpKernelControl.state false false rest zero one
        (SubexpKernelControl.emit (SubexpKernelControl.operators true (a 1).length)
          (SubexpKernelControl.setCounter 0 [] localAcc))) := by
    simpa [localAcc,SubexpKernelControl.setCounter,SubexpKernelControl.counterPort] using hd
  have h := eval_call_lifted (StructuredCalls.compiled (SubexpKernelControl.drain 5 true) 0 3)
    id productPorts d Function.injective_id productPorts_injective
    (StructuredCalls.compiled_halt_trace hd' 0 3)
  rw [ha,hb] at h
  simpa only [drainProducts, d, Nat.reduceAdd] using h

theorem drainProducts_work (v p : Bool) (rest zero one : Word) (a : Buffers) :
    Executes drainProducts (state v p true rest zero one a)
      (state false false true rest zero one (drainUpdate a)) :=
  ⟨_,drainProducts_work_eval v p rest zero one a⟩

theorem factorFold (zero one : Word) (fs : List (List SubexpTableSource.Row)) (a : Buffers) :
    fs.foldl (fun a rows => factorUpdate zero one rows a) a =
      Function.update
        (emit 0 ((fs.map (SubexpTableSource.tableCode zero one)).flatten) a) 1
        (List.replicate fs.length true ++ a 1) := by
  induction fs generalizing a with
  | nil =>
      funext i
      fin_cases i <;> simp [factorUpdate,emit]
  | cons f fs ih =>
      rw [List.foldl_cons,ih]
      funext i
      fin_cases i <;> simp [factorUpdate,emit,List.reverse_append,List.append_assoc,
        List.replicate_succ']

def factorCommand : Code :=
  productCommand SubexpTableSource.program

theorem factors_work (fs : List (List SubexpTableSource.Row)) (v p c : Bool)
    (rest zero one : Word) (a : Buffers) (h0 : a 0 = []) (h1 : a 1 = []) :
    Executes factorCommand
      (state v p c (Encoding.encodeList SubexpTableSource.encodeRows fs ++ rest) zero one a)
      (work false false true rest zero one a (factorProduct zero one fs) []) := by
  let pending := fs.foldl (fun a rows => factorUpdate zero one rows a) a
  obtain ⟨c',hs⟩ := scanFrames_work (factorBody SubexpTableSource.program)
    SubexpTableSource.encodeRows (factorUpdate zero one) (fun _ => True)
    zero one true false false
    (fun rows rest c a _ => factorBody_work rows true true c rest zero one a)
    (fun _ _ _ => trivial) fs v p c rest a trivial
  have ho := appendOne_work false true c' rest zero one pending
  have hd := drainProducts_work false false rest zero one
    (emit 0 (SubexpKernelControl.pushWord one) pending)
  let ready := drainUpdate (emit 0 (SubexpKernelControl.pushWord one) pending)
  have ht := transferBuffer_work 0 false false true rest zero one ready
  have hready : Function.update ready 0 [] = a := by
    dsimp [ready,pending]
    rw [factorFold]
    funext i
    fin_cases i <;> simp [drainUpdate,emit,h0,h1]
  have hcode : (ready 0).reverse = factorProduct zero one fs := by
    dsimp [ready,pending]
    rw [factorFold]
    simp [drainUpdate,emit,factorProduct,h0,h1,List.reverse_append,List.append_assoc]
  rw [hready,hcode] at ht
  exact executes_seq hs (executes_seq ho (executes_seq hd ht))

theorem executes_seq_iff (p q : Code) (a c : Data) :
    Executes (.seq p q) a c ↔ ∃ b, Executes p a b ∧ Executes q b c := by
  constructor
  · rintro ⟨n,h⟩
    cases h with
    | seq hp hq => exact ⟨_,⟨_,hp⟩,⟨_,hq⟩⟩
  · rintro ⟨b,hp,hq⟩
    exact executes_seq hp hq

theorem encodeList_eq_records {α : Type*} (f : α → Word) (xs : List α) :
    Encoding.encodeList f xs = (xs.map (fun x => record (f x))).flatten ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList,record,ih,List.append_assoc]

theorem close_emitted (i j : Fin 7) (bits : Word) (a : Buffers) (ha : a i = []) :
    closeUpdate i j (emit i bits a) = emit j (record (bits ++ [false])) a := by
  have hz : Function.update a i [] = a := by
    funext k
    by_cases hk : k=i
    · subst k; simp [ha]
    · simp [hk]
  simp [closeUpdate, emit, ha, List.reverse_cons, hz, Function.update_idem]

def termUpdate (zero one : Word) (t : Term) (a : Buffers) : Buffers :=
  emit 3 (record (SubexpKernelControl.encodeTerm (compiledTerm zero one t))) a

theorem termBody_work (t : Term) (c : Bool) (rest zero one : Word) (a : Buffers)
    (h0 : a 0 = []) (h1 : a 1 = []) (h2 : a 2 = []) :
    Executes (termBody SubexpTableSource.program)
      (state false false c (encodeTerm t ++ rest) zero one a)
      (state false false true rest zero one (termUpdate zero one t a)) := by
  let weightState := emit 2 (record t.weight) a
  have hw := appendCapturedRecord_work 2 false false c t.weight
    (Encoding.encodeList SubexpTableSource.encodeRows t.factors ++ rest) zero one a
  have hf := factors_work t.factors false false true rest zero one weightState
    (by simpa [weightState,emit] using h0) (by simpa [weightState,emit] using h1)
  have hr := appendRecord_work 2 false false true rest zero one
    (factorProduct zero one t.factors) weightState
  let both := emit 2 (record (factorProduct zero one t.factors)) weightState
  have hc := clearPayload_work false false true rest zero one
    (factorProduct zero one t.factors) both
  have he := closeInto_work 2 3 false false true rest zero one both
  have hresult : closeUpdate 2 3 both = termUpdate zero one t a := by
    dsimp [both,weightState]
    rw [emit_emit,close_emitted 2 3 _ a h2]
    simp [termUpdate,SubexpKernelControl.encodeTerm,compiledTerm,record,
      Encoding.encodeList,List.append_assoc]
  rw [hresult] at he
  have hend := executes_seq hr (executes_seq hc he)
  have h := executes_seq hw (executes_seq hf hend)
  simpa only [termBody, factorCommand, bufferPort_two, bufferPort_three, encodeTerm,
    List.append_assoc] using h

theorem fold_emit {α : Type*} (i : Fin 7) (f : α → Word) (xs : List α) (a : Buffers) :
    xs.foldl (fun a x => emit i (f x) a) a = emit i ((xs.map f).flatten) a := by
  induction xs generalizing a with
  | nil => funext j; by_cases h : j=i <;> simp [emit,h]
  | cons x xs ih => simp only [List.foldl_cons,ih,emit_emit,List.map_cons,List.flatten_cons]

def groupUpdate (zero one : Word) (ts : List Term) (a : Buffers) : Buffers :=
  emit 6 (record (SubexpKernelControl.encodeGroup (ts.map (compiledTerm zero one)))) a

theorem groupBody_work (ts : List Term) (c : Bool) (rest zero one : Word) (a : Buffers)
    (h0 : a 0 = []) (h1 : a 1 = []) (h2 : a 2 = []) (h3 : a 3 = []) :
    Executes (groupBody SubexpTableSource.program)
      (state false false c (encodeGroup ts ++ rest) zero one a)
      (state false false true rest zero one (groupUpdate zero one ts a)) := by
  let inv : Buffers → Prop := fun b => b 0 = [] ∧ b 1 = [] ∧ b 2 = []
  obtain ⟨c',hs⟩ := scan_work (termBody SubexpTableSource.program) encodeTerm
    (termUpdate zero one) inv zero one false false true
    (fun t rest c a h => termBody_work t c rest zero one a h.1 h.2.1 h.2.2)
    (by intro t b h; simpa [inv,termUpdate,emit] using h)
    ts false false c rest a ⟨h0,h1,h2⟩
  let pending := ts.foldl (fun a t => termUpdate zero one t a) a
  have hc := closeInto_work 3 6 false true c' rest zero one pending
  have he : closeUpdate 3 6 pending = groupUpdate zero one ts a := by
    dsimp [pending,termUpdate]
    rw [fold_emit,close_emitted 3 6 _ a h3]
    simp [groupUpdate,SubexpKernelControl.encodeGroup,encodeList_eq_records,
      List.map_map,Function.comp_def]
  rw [he] at hc
  exact executes_seq hs hc

def blockUpdate (zero one : Word) (b : Block) (a : Buffers) : Buffers :=
  emit 5 (record (SubexpKernelControl.encodeBlock (compiledBlock zero one b))) a

theorem blockBody_work (b : Block) (c : Bool) (rest zero one : Word) (a : Buffers)
    (h0 : a 0 = []) (h1 : a 1 = []) (h2 : a 2 = []) (h3 : a 3 = [])
    (h4 : a 4 = []) (h6 : a 6 = []) :
    Executes (blockBody SubexpTableSource.program)
      (state false false c (encodeBlock b ++ rest) zero one a)
      (state false false true rest zero one (blockUpdate zero one b a)) := by
  let outside := emit 4 (record b.outside) a
  have ho := appendCapturedRecord_work 4 false false c b.outside
    (Encoding.encodeList encodeGroup b.groups ++ rest) zero one a
  let inv : Buffers → Prop := fun a => a 0 = [] ∧ a 1 = [] ∧ a 2 = [] ∧ a 3 = []
  obtain ⟨c',hs⟩ := scan_work (groupBody SubexpTableSource.program) encodeGroup
    (groupUpdate zero one) inv zero one false false true
    (fun ts rest c a h => groupBody_work ts c rest zero one a h.1 h.2.1 h.2.2.1 h.2.2.2)
    (by intro ts a h; simpa [inv,groupUpdate,emit] using h)
    b.groups false false true rest outside
    (by simpa [inv,outside,emit] using And.intro h0 (And.intro h1 (And.intro h2 h3)))
  let pending := b.groups.foldl (fun a ts => groupUpdate zero one ts a) outside
  have hg := closeInto_work 6 4 false true c' rest zero one pending
  have hb := closeInto_work 4 5 false false true rest zero one (closeUpdate 6 4 pending)
  have he : closeUpdate 4 5 (closeUpdate 6 4 pending) = blockUpdate zero one b a := by
    dsimp [pending,groupUpdate]
    rw [fold_emit,close_emitted 6 4 _ outside (by simpa [outside,emit] using h6)]
    dsimp [outside]
    rw [emit_emit,close_emitted 4 5 _ a h4]
    simp [blockUpdate,compiledBlock,SubexpKernelControl.encodeBlock,SubexpKernelControl.encodeGroup,
      encodeList_eq_records,record,List.map_map,Function.comp_def,List.append_assoc]
  rw [he] at hb
  have h := executes_seq ho (executes_seq hs (executes_seq hg hb))
  simpa only [blockBody, bufferPort_four, bufferPort_five, bufferPort_six, encodeBlock,
    List.append_assoc] using h

def serviceState (input zero one : Word) : Data :=
  state false false false input zero one emptyBuffers

theorem transferOutput_work (v p c : Bool) (zero one : Word) (a : Buffers) :
    Executes (transfer 18 0) (state v p c [] zero one a)
      (state false false c (a 5).reverse zero one (Function.update a 5 [])) := by
  have h := transfer_exec 18 0 (by decide) (state v p c [] zero one a)
  have he : afterTransfer 18 0 (state v p c [] zero one a) =
      state false false c (a 5).reverse zero one (Function.update a 5 []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [state, work, readRegs, SubexpHornerProgram.triple]
    · funext i; fin_cases i <;> simp [state, work, StackRoutines.transferStacks]
  simpa only [he] using h

/-- Complete fixed-table execution from prepared rows and literal payloads
to the exact encoded weighted blocks expected by the source constructor. -/
theorem actualCommand_exec (zero one : Word) (bs : List Block) :
    Executes actualCommand (serviceState (encodeBlocks bs) zero one)
      (serviceState (assembled zero one bs) zero one) := by
  let inv : Buffers → Prop := fun a => a 0 = [] ∧ a 1 = [] ∧ a 2 = [] ∧ a 3 = [] ∧
    a 4 = [] ∧ a 6 = []
  obtain ⟨c',hs⟩ := scan_work (blockBody SubexpTableSource.program) encodeBlock
    (blockUpdate zero one) inv zero one false false true
    (fun b rest c a h => blockBody_work b c rest zero one a h.1 h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (by intro b a h; simpa [inv,blockUpdate,emit] using h)
    bs false false false [] emptyBuffers (by simp [inv,emptyBuffers])
  let pending := bs.foldl (fun a b => blockUpdate zero one b a) emptyBuffers
  have hp := pushBuffer_work 5 false false true c' [] zero one pending
  let ready := Function.update pending 5 (false :: pending 5)
  have ht := transferOutput_work false true c' zero one ready
  have hzero : Function.update ready 5 [] = emptyBuffers := by
    dsimp [ready,pending,blockUpdate]
    rw [fold_emit]
    funext i
    fin_cases i <;> simp [emit,emptyBuffers]
  have hbits : (ready 5).reverse = assembled zero one bs := by
    dsimp [ready,pending,blockUpdate]
    rw [fold_emit]
    simp [emit,emptyBuffers,assembled,SubexpKernelControl.encodeBlocks,encodeList_eq_records,
      List.reverse_cons,List.map_map,Function.comp_def]
  rw [hzero,hbits] at ht
  have hr := reset_work false false c' (assembled zero one bs) zero one [] emptyBuffers
  have h := executes_seq hs (executes_seq hp (executes_seq ht hr))
  simpa only [actualCommand, command, bufferPort_five, serviceState, state, List.append_nil,
    encodeBlocks] using h

theorem actualProgram_trace (zero one : Word) (bs : List Block) :
    ∃ n, Trace actualProgram n
      ((serviceState (encodeBlocks bs) zero one).withPC (some actualProgram.entry))
      ((serviceState (assembled zero one bs) zero one).withPC none) := by
  obtain ⟨n,hn⟩ := actualCommand_exec zero one bs
  exact ⟨n+1,StructuredCalls.compiled_halt_trace hn 0 0⟩

end SubexponentialSAT.SubexpBlockAssembly

end OAI.Algorithms
