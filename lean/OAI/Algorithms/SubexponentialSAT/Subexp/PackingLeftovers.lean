import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftoverEmitter
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorMapProgram

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 18
abbrev Code := Cmd 8 18
abbrev unary (n : ℕ) := List.replicate n true
abbrev Records := List (List Bool × List Bool)

def data (regs : Fin 8 → Bool)
    (work query covered source payload rank address storage metadata addresses vertex : List Bool) : Data :=
  ⟨regs, ![work,[],query,[],[],[],covered,source,payload,[],rank,address,storage,metadata,addresses,vertex,[],[]]⟩

def state (regs : Fin 8 → Bool)
    (covered source rank address storage metadata addresses : List Bool) : Data :=
  data regs [] [] covered source [] rank address storage metadata addresses []

theorem data_stacks (regs : Fin 8 → Bool)
    (work query covered source payload rank address storage metadata addresses vertex : List Bool)
    (i : Fin 18) :
    (data regs work query covered source payload rank address storage metadata addresses vertex).stacks i =
      if i=0 then work else if i=2 then query else if i=6 then covered
      else if i=7 then source else if i=8 then payload else if i=10 then rank
      else if i=11 then address else if i=12 then storage else if i=13 then metadata
      else if i=14 then addresses else if i=15 then vertex else [] := by
  fin_cases i <;> rfl

def queryRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def queryStacks : Fin 6 → Fin 18 := Fin.castAdd 12
theorem queryRegs_injective : Function.Injective queryRegs := Fin.castAdd_injective 5 3
theorem queryStacks_injective : Function.Injective queryStacks := Fin.castAdd_injective 6 12

def mergeRegs (base : Fin 8 → Bool) (localRegs : Fin 5 → Bool) : Fin 8 → Bool :=
  fun i => if h : i.val < 5 then localRegs ⟨i.val,h⟩ else base i

def queryCall : Code := .call
  (ProgramLinking.liftProgram PackingCoveredQuery.program queryRegs queryStacks)

theorem query_eval (records : Records) (query : List Bool) (regs : Fin 8 → Bool)
    (source payload rank address storage metadata addresses vertex : List Bool) :
    ∃ n ≤ PackingCoveredQuery.budget query records+1, ∃ rf,
      Eval queryCall n
        (data regs (SelectorProgram.rawRecords records) query.reverse
          (SelectorProgram.rawRecords records) source payload rank address storage metadata addresses vertex)
        (data rf [] [] (SelectorProgram.rawRecords records) source payload rank address storage metadata addresses vertex) ∧
      rf 4 = (records.lookup query).isSome := by
  let a := data regs (SelectorProgram.rawRecords records) query.reverse
    (SelectorProgram.rawRecords records) source payload rank address storage metadata addresses vertex
  obtain ⟨n,hn,rs,ht,hflag⟩ := PackingCoveredQuery.program_trace query records (regs ∘ queryRegs)
  let rf := mergeRegs regs rs
  let b := data rf [] [] (SelectorProgram.rawRecords records) source payload rank address storage metadata addresses vertex
  have ha : embedState queryRegs queryStacks a
      (PackingCoveredQuery.state (regs ∘ queryRegs) (SelectorProgram.rawRecords records) query.reverse []) = a := by
    apply SelectorMapProgram.embed_eq _ _ queryRegs_injective queryStacks_injective
    · intros; rfl
    · intro i
      fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState queryRegs queryStacks a (PackingCoveredQuery.state rs [] [] []) = b := by
    apply SelectorMapProgram.embed_eq _ _ queryRegs_injective queryStacks_injective
    · intro i
      simp [b,rf,mergeRegs,queryRegs,PackingCoveredQuery.state,SubexpRecordScan.recordState,data,i.isLt]
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      have hn : ¬ i.val < 5 := by
        intro h
        exact hi ⟨⟨i.val,h⟩,Fin.ext rfl⟩
      simp [b,rf,mergeRegs,hn,a,data]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2,h.symm⟩
      simp only [a,b,data_stacks,ite_eq_right h0,ite_eq_right h2]
  have he := eval_call_lifted PackingCoveredQuery.program queryRegs queryStacks a
    queryRegs_injective queryStacks_injective ht
  rw [ha,hb] at he
  refine ⟨n,hn,rf,he,?_⟩
  simpa [rf,mergeRegs] using hflag

def emitterStacks : Fin 9 → Fin 18 := ![15,10,11,12,13,14,9,16,17]
theorem emitterStacks_injective : Function.Injective emitterStacks := by decide

def emitCall : Code := .call
  (ProgramLinking.liftProgram PackingLeftoverEmitter.program id emitterStacks)

theorem emit_eval (regs : Fin 8 → Bool)
    (covered source rank address storage metadata addresses vertex : List Bool) :
    ∃ rf, Eval emitCall (PackingLeftoverEmitter.commandCost vertex rank address+1)
      (data regs [] [] covered source [] rank address storage metadata addresses vertex)
      (data rf [] [] covered source [] (true::rank) (true::address)
        (PackingLeftoverEmitter.storageOutput vertex storage)
        (PackingLeftoverEmitter.metadataOutput vertex rank metadata)
        (PackingLeftoverEmitter.addressOutput vertex address addresses) []) := by
  let a := data regs [] [] covered source [] rank address storage metadata addresses vertex
  obtain ⟨rf,ht⟩ := PackingLeftoverEmitter.program_trace vertex rank address storage metadata addresses regs
  let b := data rf [] [] covered source [] (true::rank) (true::address)
    (PackingLeftoverEmitter.storageOutput vertex storage)
    (PackingLeftoverEmitter.metadataOutput vertex rank metadata)
    (PackingLeftoverEmitter.addressOutput vertex address addresses) []
  have ha : embedState id emitterStacks a
      (PackingLeftoverEmitter.state regs vertex rank address storage metadata addresses) = a := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id emitterStacks_injective
    · intros; rfl
    · intro i
      fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState id emitterStacks a
      (PackingLeftoverEmitter.state rf [] (true::rank) (true::address)
        (PackingLeftoverEmitter.storageOutput vertex storage)
        (PackingLeftoverEmitter.metadataOutput vertex rank metadata)
        (PackingLeftoverEmitter.addressOutput vertex address addresses)) = b := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id emitterStacks_injective
    · intros; rfl
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      exact (hi ⟨i,rfl⟩).elim
    · intro i hi
      have h15 : i ≠ 15 := fun h => hi ⟨0,h.symm⟩
      have h10 : i ≠ 10 := fun h => hi ⟨1,h.symm⟩
      have h11 : i ≠ 11 := fun h => hi ⟨2,h.symm⟩
      have h12 : i ≠ 12 := fun h => hi ⟨3,h.symm⟩
      have h13 : i ≠ 13 := fun h => hi ⟨4,h.symm⟩
      have h14 : i ≠ 14 := fun h => hi ⟨5,h.symm⟩
      simp only [a,b,data_stacks,ite_eq_right h15,ite_eq_right h10,ite_eq_right h11,ite_eq_right h12,ite_eq_right h13,ite_eq_right h14]
  have he := eval_call_lifted PackingLeftoverEmitter.program id emitterStacks a
    Function.injective_id emitterStacks_injective ht
  rw [ha,hb] at he
  exact ⟨rf,he⟩

def clearVertex : Code := .call (StackRoutines.clearProgram 15 0 1)

theorem clearVertex_eval (regs : Fin 8 → Bool)
    (covered source rank address storage metadata addresses vertex : List Bool) :
    Eval clearVertex (2*vertex.length+3)
      (data regs [] [] covered source [] rank address storage metadata addresses vertex)
      (data (readRegs regs 0 1 none) [] [] covered source [] rank address storage metadata addresses []) := by
  let a := data regs [] [] covered source [] rank address storage metadata addresses vertex
  have h := TupleProgram.clear_eval (15 : Fin 18) (0 : Fin 8) 1 a
  have he : (⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks 15 a.stacks⟩ : Data) =
      data (readRegs regs 0 1 none) [] [] covered source [] rank address storage metadata addresses [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [a,data,StackRoutines.clearStacks]
  rw [he] at h
  exact h

def parserRegs (regs : Fin 8 → Bool) (tag present found : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 tag) 6 present) 7 found

def resetParser : Code := .seq (.base (.atom (.set 5 false)))
  (.seq (.base (.atom (.set 6 true))) (.base (.atom (.set 7 false))))

theorem resetParser_eval (d : Data) :
    Eval resetParser 3 d ⟨parserRegs d.regs false true false,d.stacks⟩ := by
  exact (Eval.base (.atom (.set 5 false) d)).seq
    ((Eval.base (.atom (.set 6 true) _)).seq (Eval.base (.atom (.set 7 false) _)))

def callback : Code := .seq (transfer 8 15)
  (.seq (MatrixProgramSupport.copy 6 0 9)
    (.seq (MatrixProgramSupport.copy 15 2 9)
      (.seq queryCall (.seq (.ite 4 clearVertex emitCall) resetParser))))

structure Snapshot where
  rank : ℕ
  address : ℕ
  storage : List Bool
  metadata : List Bool
  addresses : List Bool

def appendVertex (s : Snapshot) (v : ℕ) : Snapshot :=
  ⟨s.rank+1,s.address+1,
    PackingLeftoverEmitter.storageOutput (unary v) s.storage,
    PackingLeftoverEmitter.metadataOutput (unary v) (unary s.rank) s.metadata,
    PackingLeftoverEmitter.addressOutput (unary v) (unary s.address) s.addresses⟩

def covered (records : Records) (v : ℕ) : Bool := (records.lookup (unary v)).isSome

def advance (records : Records) (s : Snapshot) (v : ℕ) : Snapshot :=
  if covered records v then s else appendVertex s v

def configured (regs : Fin 8 → Bool) (records : Records) (source payload : List Bool)
    (s : Snapshot) (vertex : List Bool) : Data :=
  data regs [] [] (SelectorProgram.rawRecords records) source payload (unary s.rank) (unary s.address)
    s.storage s.metadata s.addresses vertex

def callbackCost (records : Records) (v : ℕ) (s : Snapshot) : ℕ :=
  9*(SelectorProgram.rawRecords records).length+56*v+
    5*SelectorProgram.scanBudget (unary v) records+31*s.rank+15*s.address+143

theorem callback_eval (records : Records) (v : ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (source : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ callbackCost records v s ∧
      Eval callback n (configured regs records source (unary v) s [])
        (configured rf records source [] (advance records s v) []) ∧
      rf 5 = false ∧ rf 6 = true ∧ rf 7 = false := by
  let a0 := configured regs records source (unary v) s []
  obtain ⟨r1,h1,hs1⟩ := transfer_eval (8 : Fin 18) 15 (by decide) a0
  let a1 := configured r1.regs records source [] s (unary v)
  have he1 : r1=a1 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs1]
    funext i
    fin_cases i <;> simp [a0,configured,data,StackRoutines.transferStacks]
  rw [he1] at h1
  obtain ⟨r2,h2,hs2⟩ := copy_eval (6 : Fin 18) 0 9 (by decide) (by decide) (by decide) a1 rfl
  let a2 := data r2.regs (SelectorProgram.rawRecords records) []
    (SelectorProgram.rawRecords records) source [] (unary s.rank) (unary s.address)
    s.storage s.metadata s.addresses (unary v)
  have he2 : r2=a2 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs2]
    funext i
    fin_cases i <;> simp [a1,configured,data,StackRoutines.copyStacks]
  rw [he2] at h2
  obtain ⟨r3,h3,hs3⟩ := copy_eval (15 : Fin 18) 2 9 (by decide) (by decide) (by decide) a2 rfl
  let a3 := data r3.regs (SelectorProgram.rawRecords records) (unary v)
    (SelectorProgram.rawRecords records) source [] (unary s.rank) (unary s.address)
    s.storage s.metadata s.addresses (unary v)
  have he3 : r3=a3 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs3]
    funext i
    fin_cases i <;> simp [a2,data,StackRoutines.copyStacks]
  rw [he3] at h3
  obtain ⟨nq,hnq,rq,hq,hflag⟩ := query_eval records (unary v) r3.regs source []
    (unary s.rank) (unary s.address) s.storage s.metadata s.addresses (unary v)
  simp only [List.reverse_replicate] at hq
  let a4 := configured rq records source [] s (unary v)
  have hbranch : ∃ nb rb, nb ≤ 44*v+31*s.rank+15*s.address+103 ∧
      Eval (.ite 4 clearVertex emitCall) nb a4
        (configured rb records source [] (advance records s v) []) := by
    cases hc : covered records v with
    | true =>
        have hf : rq 4 = true := hflag.trans hc
        have he := clearVertex_eval rq (SelectorProgram.rawRecords records) source
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses (unary v)
        refine ⟨2*v+4,readRegs rq 0 1 none,by omega,?_⟩
        simpa [a4,configured,advance,hc] using Eval.ite_true hf he
    | false =>
        have hf : rq 4 = false := hflag.trans hc
        obtain ⟨rf,he⟩ := emit_eval rq (SelectorProgram.rawRecords records) source
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses (unary v)
        refine ⟨44*v+31*s.rank+15*s.address+103,rf,le_rfl,?_⟩
        simpa [a4,configured,advance,hc,appendVertex,PackingLeftoverEmitter.commandCost,
          List.replicate_succ,Nat.add_assoc] using Eval.ite_false hf he
  obtain ⟨nb,rb,hnb,hb⟩ := hbranch
  have hr := resetParser_eval (configured rb records source [] (advance records s v) [])
  have hrun := h1.seq (h2.seq (h3.seq (hq.seq (hb.seq hr))))
  refine ⟨_,parserRegs rb false true false,?_,hrun,?_,?_,?_⟩
  · change (3*(unary v).length+3)+((7*(SelectorProgram.rawRecords records).length+5)+
      ((7*(unary v).length+5)+(nq+(nb+3)))) ≤ callbackCost records v s
    simp only [List.length_replicate]
    dsimp [PackingCoveredQuery.budget] at hnq
    simp only [List.length_replicate] at hnq
    dsimp [callbackCost]
    omega
  · simp [parserRegs]
  · simp [parserRegs]
  · simp [parserRegs]

def ports : RecordPrograms.Ports 8 18 :=
  ⟨5,6,7,7,8,by decide,by decide,by decide,by decide⟩

theorem parser_state (regs : Fin 8 → Bool) (records : Records) (s : Snapshot)
    (source payload vertex newSource newPayload : List Bool) (tag present found : Bool) :
    RecordPrograms.state ports (configured regs records source payload s vertex)
      tag present found newSource newPayload =
    configured (parserRegs regs tag present found) records newSource newPayload s vertex := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [configured,data,ports]

theorem parserRegs_self (regs : Fin 8 → Bool) (tag present found : Bool)
    (h5 : regs 5=tag) (h6 : regs 6=present) (h7 : regs 7=found) :
    parserRegs regs tag present found=regs := by
  funext i
  by_cases h : i=7
  · subst i; simp [parserRegs,h7]
  by_cases h' : i=6
  · subst i; simp [parserRegs,h6]
  by_cases h'' : i=5
  · subst i; simp [parserRegs,h5]
  simp [parserRegs,h,h',h'']

def iterationCost (records : Records) : List ℕ → Snapshot → ℕ
  | [], _ => 0
  | v::vertices, s => 6*v+callbackCost records v s+7+
      iterationCost records vertices (advance records s v)

def command : Code := RecordPrograms.iterate ports callback
def program := compiled command 7 12
def traceCost (records : Records) (vertices : List ℕ) (s : Snapshot) : ℕ :=
  4+iterationCost records vertices s

theorem loop_eval (records : Records) (vertices : List ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 1+iterationCost records vertices s ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (configured regs records [] [] s [])
          (vertices.map unary) suffix)
        (RecordPrograms.state ports
          (configured rf records [] [] (vertices.foldl (advance records) s) [])
          false true false suffix []) := by
  induction vertices generalizing s regs with
  | nil =>
      refine ⟨1,regs,by simp [iterationCost],?_⟩
      simpa only [List.map_nil,RecordPrograms.afterTag,List.foldl_nil] using
        (Eval.while_false (body := RecordPrograms.body ports callback)
          (a := RecordPrograms.state ports (configured regs records [] [] s [])
            false true false suffix []) (by simp))
  | cons v vertices ih =>
      let a := configured regs records [] [] s []
      let tail := Encoding.encodeList id (vertices.map unary) ++ suffix
      have hreader : Eval (RecordPrograms.reader ports) (6*v+4)
          (RecordPrograms.afterTag ports a ((v::vertices).map unary) suffix)
          (RecordPrograms.state ports a false true false tail (unary v)) := by
        simpa only [List.map_cons,RecordPrograms.afterTag,List.append_nil,
          List.length_replicate,List.reverse_replicate] using
          RecordPrograms.reader_eval ports a (unary v) tail [] true true false
      obtain ⟨nc,rc,hnc,hc,h5,h6,h7⟩ := callback_eval records v s
        (parserRegs regs false true false) tail
      let b := configured rc records [] [] (advance records s v) []
      have hcb : Eval callback nc
          (RecordPrograms.state ports a false true false tail (unary v))
          (RecordPrograms.state ports b false true false tail []) := by
        simpa only [a,b,parser_state,parserRegs_self rc false true false h5 h6 h7] using hc
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports b false true false tail [])
          (RecordPrograms.afterTag ports b (vertices.map unary) suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports b (vertices.map unary) suffix false true
      obtain ⟨nr,rf,hnr,hr⟩ := ih (advance records s v) rc
      have hrun := Eval.while_true
        (show (RecordPrograms.afterTag ports a ((v::vertices).map unary) suffix).regs ports.tag=true by
          simp [RecordPrograms.afterTag]) (hreader.seq (hcb.seq hbranch)) hr
      refine ⟨6*v+4+(nc+2)+nr+1,rf,?_,?_⟩
      · simp only [iterationCost]
        omega
      · simpa only [RecordPrograms.loop,RecordPrograms.body,a,b,List.foldl_cons] using hrun

/-- Complete scan of actual original-vertex records. The saved covered table
is unchanged, and all work ports are cleared. -/
theorem command_eval (records : Records) (vertices : List ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n+1 ≤ traceCost records vertices s ∧
      Eval command n
        (state regs (SelectorProgram.rawRecords records)
          (ProgramEncoding.encodeRecords (vertices.map unary) ++ suffix)
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses)
        (state rf (SelectorProgram.rawRecords records) suffix
          (unary (vertices.foldl (advance records) s).rank)
          (unary (vertices.foldl (advance records) s).address)
          (vertices.foldl (advance records) s).storage
          (vertices.foldl (advance records) s).metadata
          (vertices.foldl (advance records) s).addresses) := by
  let a := configured regs records [] [] s []
  obtain ⟨n,rf,hn,he⟩ := loop_eval records vertices s regs suffix
  have hset := RecordPrograms.set_found_eval ports a (regs 5) (regs 6) (regs 7) false
    (ProgramEncoding.encodeRecords (vertices.map unary) ++ suffix) []
  have hpop := RecordPrograms.pop_list_eval ports a (vertices.map unary) suffix (regs 5) (regs 6)
  have hrun := hset.seq (hpop.seq he)
  rw [parser_state, parser_state] at hrun
  refine ⟨1+(1+n),parserRegs rf false true false,by dsimp [traceCost]; omega,?_⟩
  simpa only [command,RecordPrograms.iterate,a,configured,data,state,
    parserRegs_self regs (regs 5) (regs 6) (regs 7) rfl rfl rfl] using hrun

theorem program_trace (records : Records) (vertices : List ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ traceCost records vertices s ∧
      Trace program n
        ((state regs (SelectorProgram.rawRecords records)
          (ProgramEncoding.encodeRecords (vertices.map unary) ++ suffix)
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses).withPC (some program.entry))
        ((state rf (SelectorProgram.rawRecords records) suffix
          (unary (vertices.foldl (advance records) s).rank)
          (unary (vertices.foldl (advance records) s).address)
          (vertices.foldl (advance records) s).storage
          (vertices.foldl (advance records) s).metadata
          (vertices.foldl (advance records) s).addresses).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval records vertices s regs suffix
  exact ⟨n+1,rf,hn,compiled_halt_trace he 7 12⟩

theorem program_primitive (records : Records) (vertices : List ℕ) (s : Snapshot)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * traceCost records vertices s)
      (BitProgram.primitiveCfg program
        ((state regs (SelectorProgram.rawRecords records)
          (ProgramEncoding.encodeRecords (vertices.map unary) ++ suffix)
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state rf (SelectorProgram.rawRecords records) suffix
          (unary (vertices.foldl (advance records) s).rank)
          (unary (vertices.foldl (advance records) s).address)
          (vertices.foldl (advance records) s).storage
          (vertices.foldl (advance records) s).metadata
          (vertices.foldl (advance records) s).addresses).withPC none)) := by
  obtain ⟨n,rf,hn,he⟩ := program_trace records vertices s regs suffix
  exact ⟨rf,BitProgram.primitive_execution program ⟨n,hn,he⟩⟩

def leftovers (records : Records) (vertices : List ℕ) : List ℕ :=
  vertices.filter (fun v => !(covered records v))

/-- Filtering is a specification of the proved scan; the machine itself
performs the selector call for every vertex. -/
theorem fold_advance_eq (records : Records) (vertices : List ℕ) (s : Snapshot) :
    vertices.foldl (advance records) s = (leftovers records vertices).foldl appendVertex s := by
  induction vertices generalizing s with
  | nil => rfl
  | cons v vertices ih =>
      cases hc : covered records v <;>
        simp [List.foldl_cons,advance,leftovers,hc,ih]

theorem append_fold_rank (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).rank = s.rank+vertices.length := by
  induction vertices generalizing s with
  | nil => simp
  | cons v vertices ih =>
      rw [List.foldl_cons,ih]
      change s.rank+1+vertices.length = s.rank+(vertices.length+1)
      omega

theorem append_fold_address (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).address = s.address+vertices.length := by
  induction vertices generalizing s with
  | nil => simp
  | cons v vertices ih =>
      rw [List.foldl_cons,ih]
      change s.address+1+vertices.length = s.address+(vertices.length+1)
      omega

theorem final_counters (records : Records) (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl (advance records) s).rank = s.rank+(leftovers records vertices).length ∧
    (vertices.foldl (advance records) s).address = s.address+(leftovers records vertices).length := by
  rw [fold_advance_eq]
  exact ⟨append_fold_rank _ _,append_fold_address _ _⟩

def storageRecords (vertices : List ℕ) : List Bool :=
  vertices.flatMap (fun v => true :: Encoding.frame (unary v))

theorem append_fold_storage (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).storage = (storageRecords vertices).reverse ++ s.storage := by
  induction vertices generalizing s with
  | nil => simp [storageRecords]
  | cons v vertices ih =>
      simpa [storageRecords,appendVertex,PackingLeftoverEmitter.storageOutput,
        List.reverse_append,List.append_assoc] using ih (appendVertex s v)

theorem final_storage (records : Records) (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl (advance records) s).storage =
      (storageRecords (leftovers records vertices)).reverse ++ s.storage := by
  rw [fold_advance_eq,append_fold_storage]

def metadataRecords : ℕ → List ℕ → Records
  | _, [] => []
  | rank, v::vertices =>
      (unary v,PackingLeftoverEmitter.metadataPayload (unary rank)) ::
        metadataRecords (rank+1) vertices

def addressRecords : ℕ → List ℕ → Records
  | _, [] => []
  | address, v::vertices => (unary v,unary address) :: addressRecords (address+1) vertices

theorem rawRecords_append (a b : Records) :
    SelectorProgram.rawRecords (a++b) =
      SelectorProgram.rawRecords a ++ SelectorProgram.rawRecords b := by
  simp [SelectorProgram.rawRecords]

@[simp] theorem rawRecords_singleton (key value : List Bool) :
    SelectorProgram.rawRecords [(key,value)] = Encoding.frame key ++ Encoding.frame value := by
  simp [SelectorProgram.rawRecords]

theorem append_fold_metadata (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).metadata =
      SelectorProgram.rawRecords (metadataRecords s.rank vertices).reverse ++ s.metadata := by
  induction vertices generalizing s with
  | nil => simp [metadataRecords,SelectorProgram.rawRecords]
  | cons v vertices ih =>
      simpa [metadataRecords,List.reverse_cons,rawRecords_append,appendVertex,
        PackingLeftoverEmitter.metadataOutput,List.append_assoc] using ih (appendVertex s v)

theorem append_fold_addresses (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).addresses =
      SelectorProgram.rawRecords (addressRecords s.address vertices).reverse ++ s.addresses := by
  induction vertices generalizing s with
  | nil => simp [addressRecords,SelectorProgram.rawRecords]
  | cons v vertices ih =>
      simpa [addressRecords,List.reverse_cons,rawRecords_append,appendVertex,
        PackingLeftoverEmitter.addressOutput,List.append_assoc] using ih (appendVertex s v)

theorem final_metadata (records : Records) (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl (advance records) s).metadata =
      SelectorProgram.rawRecords (metadataRecords s.rank (leftovers records vertices)).reverse ++ s.metadata := by
  rw [fold_advance_eq,append_fold_metadata]

theorem final_addresses (records : Records) (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl (advance records) s).addresses =
      SelectorProgram.rawRecords (addressRecords s.address (leftovers records vertices)).reverse ++ s.addresses := by
  rw [fold_advance_eq,append_fold_addresses]

theorem advance_rank_le (records : Records) (s : Snapshot) (v : ℕ) :
    (advance records s v).rank ≤ s.rank+1 := by
  unfold advance
  split <;> simp [appendVertex]

theorem advance_address_le (records : Records) (s : Snapshot) (v : ℕ) :
    (advance records s v).address ≤ s.address+1 := by
  unfold advance
  split <;> simp [appendVertex]

theorem callbackCost_le (records : Records) (v V R A : ℕ) (s : Snapshot)
    (hv : v ≤ V) (hr : s.rank ≤ R) (ha : s.address ≤ A) :
    callbackCost records v s ≤
      (45*V+109)*(SelectorProgram.rawRecords records).length+56*V+31*R+15*A+148 := by
  have hs := PackingCoveredQuery.scanBudget_le (unary v) records
  simp only [List.length_replicate] at hs
  calc
    callbackCost records v s ≤
        (45*v+109)*(SelectorProgram.rawRecords records).length+56*v+31*s.rank+15*s.address+148 := by
      dsimp [callbackCost]
      nlinarith
    _ ≤ _ := by gcongr

theorem iterationCost_le (records : Records) (vertices : List ℕ) (s : Snapshot) (V R A : ℕ)
    (hv : ∀ v ∈ vertices, v ≤ V)
    (hr : s.rank+vertices.length ≤ R) (ha : s.address+vertices.length ≤ A) :
    iterationCost records vertices s ≤ vertices.length *
      ((45*V+109)*(SelectorProgram.rawRecords records).length+62*V+31*R+15*A+155) := by
  induction vertices generalizing s with
  | nil => simp [iterationCost]
  | cons v vertices ih =>
      have hvv := hv v (by simp)
      have hcb := callbackCost_le records v V R A s hvv (by simp only [List.length_cons] at hr; omega)
        (by simp only [List.length_cons] at ha; omega)
      have hr' := advance_rank_le records s v
      have ha' := advance_address_le records s v
      have ht := ih (advance records s v) (fun x hx => hv x (by simp [hx]))
        (by simp only [List.length_cons] at hr; omega)
        (by simp only [List.length_cons] at ha; omega)
      let C := (45*V+109)*(SelectorProgram.rawRecords records).length+62*V+31*R+15*A+155
      have hhead : 6*v+callbackCost records v s+7 ≤ C := by
        dsimp [C]
        omega
      change 6*v+callbackCost records v s+7+
        iterationCost records vertices (advance records s v) ≤ (vertices.length+1)*C
      calc
        _ ≤ C+vertices.length*C := Nat.add_le_add hhead ht
        _ = _ := by ring

/-- Polynomial bound in serialized covered-table size, vertex count, largest
unary vertex, and the initial unary counters. -/
theorem traceCost_le (records : Records) (vertices : List ℕ) (s : Snapshot) (V : ℕ)
    (hv : ∀ v ∈ vertices, v ≤ V) :
    traceCost records vertices s ≤ 4+vertices.length *
      ((45*V+109)*(SelectorProgram.rawRecords records).length+62*V+
        31*(s.rank+vertices.length)+15*(s.address+vertices.length)+155) := by
  exact Nat.add_le_add_left (iterationCost_le records vertices s V
    (s.rank+vertices.length) (s.address+vertices.length) hv le_rfl le_rfl) 4

theorem range_command_eval (records : Records) (D : ℕ) (s : Snapshot) (regs : Fin 8 → Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n+1 ≤ traceCost records (List.range D) s ∧
      Eval command n
        (state regs (SelectorProgram.rawRecords records)
          (ProgramEncoding.encodeRecords ((List.range D).map unary))
          (unary s.rank) (unary s.address) s.storage s.metadata s.addresses)
        (state rf (SelectorProgram.rawRecords records) []
          (unary ((List.range D).foldl (advance records) s).rank)
          (unary ((List.range D).foldl (advance records) s).address)
          ((List.range D).foldl (advance records) s).storage
          ((List.range D).foldl (advance records) s).metadata
          ((List.range D).foldl (advance records) s).addresses) := by
  simpa only [List.append_nil] using command_eval records (List.range D) s regs []

theorem range_traceCost_le (records : Records) (D : ℕ) (s : Snapshot) :
    traceCost records (List.range D) s ≤ 4+D *
      ((45*D+109)*(SelectorProgram.rawRecords records).length+62*D+
        31*(s.rank+D)+15*(s.address+D)+155) := by
  simpa only [List.length_range] using traceCost_le records (List.range D) s D
    (fun v hv => Nat.le_of_lt (List.mem_range.mp hv))

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
