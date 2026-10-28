import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorMapProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BucketProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPlanAlphabetProgram

namespace OAI.Algorithms

/-! Gathering the actual assignment type at every vertex before packing. -/

namespace SubexponentialSAT.Subexp.PackingVertexLabels

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 15

def ports : RecordPrograms.Ports 8 15 :=
  ⟨5, 6, 7, 10, 11, by decide, by decide, by decide, by decide⟩

def state (regs : Fin 8 → Bool) (array output width plan source payload index records temp : List Bool) :
    Data :=
  ⟨regs, ![array, output, [], width, [], [], [], [], plan, [],
    source, payload, index, records, temp]⟩

def gatherRegs (i : Fin 3) : Fin 8 := Fin.castAdd 5 i
def gatherPorts (i : Fin 10) : Fin 15 := Fin.castAdd 5 i

theorem gatherRegs_injective : Function.Injective gatherRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 8 => z.val) h)

theorem gatherPorts_injective : Function.Injective gatherPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 15 => z.val) h)

abbrev gatherCall : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram GatherProgram.program gatherRegs gatherPorts)

abbrev sequence (cs : List (Cmd 8 15)) : Cmd 8 15 :=
  cs.foldr Cmd.seq (.base .skip)

abbrev callback : Cmd 8 15 := sequence [
  transfer 11 14,
  readWord 14 8 2 (by decide),
  .base (.atom (.set 0 false)),
  .base (.atom (.set 1 false)),
  .base (.atom (.set 2 false)),
  gatherCall,
  MatrixProgramSupport.copy 12 14 2,
  emitFrame 14 13 2 (by decide),
  emitFrame 1 13 2 (by decide),
  TupleProgram.pushConst 12 0 true,
  .base (.atom (.set 5 false)),
  .base (.atom (.set 6 true)),
  .base (.atom (.set 7 false))]

abbrev command : Cmd 8 15 := RecordPrograms.iterate ports callback
def program := compiled command 10 13

def planPayload (plan : List ℕ) : List Bool :=
  Encoding.frame (ProgramEncoding.encodeRecords (GatherProgram.indexRecords plan))

def labelRecords (rows : List (List Bool)) (plans : List (List ℕ)) (start : ℕ) :
    List BucketProgram.Record :=
  plans.zipWith (fun plan i => (GatherProgram.gathered rows plan, List.replicate i true))
    (List.range' start plans.length)

def callbackCost (width planBytes index : ℕ) : ℕ :=
  200 * (width + planBytes + index + 1) ^ 2

def planBytes (plan : List ℕ) : List Bool :=
  ProgramEncoding.encodeRecords (GatherProgram.indexRecords plan)

theorem gathered_eq_readPlan (rows : List (List Bool)) (plan : List ℕ) :
    GatherProgram.gathered rows plan = (ReadPlan.gather [] rows plan).flatten := by
  simp [GatherProgram.gathered, ReadPlan.gather, List.flatMap]

theorem state_stacks (regs : Fin 8 → Bool)
    (array output width plan source payload index records temp : List Bool) (i : Fin 15) :
    (state regs array output width plan source payload index records temp).stacks i =
      if i = 0 then array else if i = 1 then output else if i = 3 then width
      else if i = 8 then plan else if i = 10 then source else if i = 11 then payload
      else if i = 12 then index else if i = 13 then records else if i = 14 then temp else [] := by
  fin_cases i <;> rfl

private theorem state_of_stacks (d : Data) (regs : Fin 8 → Bool)
    (array output width plan source payload index records temp : List Bool)
    (h : d.stacks =
      (state regs array output width plan source payload index records temp).stacks) :
    d = state d.regs array output width plan source payload index records temp := by
  apply congrArg₂ StructuredProgram.State.mk rfl h

def setData (i : Fin 8) (b : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs i b, d.stacks⟩

theorem set_eval (i : Fin 8) (b : Bool) (d : Data) :
    Eval (.base (.atom (.set i b))) 1 d (setData i b d) := by
  exact .base (.atom _ _)

def parserRegs (regs : Fin 8 → Bool) (tag present found : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 tag) 6 present) 7 found

theorem parser_state (regs : Fin 8 → Bool)
    (array output width plan source payload index records temp newSource newPayload : List Bool)
    (tag present found : Bool) :
    RecordPrograms.state ports
      (state regs array output width plan source payload index records temp)
      tag present found newSource newPayload =
    state (parserRegs regs tag present found)
      array output width plan newSource newPayload index records temp := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports, state]

theorem parserRegs_self (regs : Fin 8 → Bool) (tag present found : Bool)
    (h5 : regs 5 = tag) (h6 : regs 6 = present) (h7 : regs 7 = found) :
    parserRegs regs tag present found = regs := by
  funext i
  by_cases h : i = 7
  · subst i; simp [parserRegs, h7]
  by_cases h' : i = 6
  · subst i; simp [parserRegs, h6]
  by_cases h'' : i = 5
  · subst i; simp [parserRegs, h5]
  simp [parserRegs, h, h', h'']

/-- Lift the checked gather machine into the first ten work ports. -/
theorem gatherCall_eval (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (regs : Fin 8 → Bool) (source index records : List Bool)
    (h0 : regs 0 = false) (h1 : regs 1 = false) (h2 : regs 2 = false)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ n, n ≤ GatherProgram.traceCost rows width.length plan ∧
      Eval gatherCall n
        (state regs rows.flatten [] width (planBytes plan) source [] index records [])
        (state regs rows.flatten (GatherProgram.gathered rows plan) width [] source [] index records []) := by
  let a := state regs rows.flatten [] width (planBytes plan) source [] index records []
  let b := state regs rows.flatten (GatherProgram.gathered rows plan) width [] source [] index records []
  obtain ⟨n, hn, ht⟩ := GatherProgram.program_run rows width plan hrows hplan
  have ha : embedState gatherRegs gatherPorts a (GatherProgram.inputState rows width plan) = a := by
    apply SelectorMapProgram.embed_eq _ _ gatherRegs_injective gatherPorts_injective
    · intro i
      fin_cases i <;> simp [a, state, gatherRegs, GatherProgram.inputState,
        GatherProgram.baseState, RecordPrograms.state, GatherProgram.ports, h0, h1, h2]
    · intro i
      fin_cases i <;> simp [a, state, gatherPorts, GatherProgram.inputState,
        GatherProgram.baseState, RecordPrograms.state, GatherProgram.ports, planBytes]
    · intros; rfl
    · intros; rfl
  have hb : embedState gatherRegs gatherPorts a (GatherProgram.outputState rows width plan) = b := by
    apply SelectorMapProgram.embed_eq _ _ gatherRegs_injective gatherPorts_injective
    · intro i
      fin_cases i <;> simp [b, state, gatherRegs, GatherProgram.outputState, h0, h1, h2]
    · intro i
      fin_cases i <;> simp [b, state, gatherPorts, GatherProgram.outputState]
    · intros; rfl
    · intro i hi
      have hi1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have hi8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
      simp only [a, b, state_stacks, ite_eq_right hi1, ite_eq_right hi8]
  have he := eval_call_lifted GatherProgram.program gatherRegs gatherPorts a
    gatherRegs_injective gatherPorts_injective ht
  rw [ha, hb] at he
  exact ⟨n, hn, he⟩

/-- Each callback consumes the actual framed plan, performs the persistent
array reads, and prepends one raw `(type, vertex)` record. -/
theorem callback_eval (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (regs : Fin 8 → Bool) (source records : List Bool) (index : ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      Eval callback n
        (state regs rows.flatten [] width [] source (planPayload plan).reverse
          (List.replicate index true) records [])
        (state rf rows.flatten [] width [] source [] (List.replicate (index+1) true)
          (Encoding.frame (GatherProgram.gathered rows plan) ++
            (Encoding.frame (List.replicate index true) ++ records)) []) ∧
      rf 5 = false ∧ rf 6 = true ∧ rf 7 = false ∧
      n ≤ callbackCost width.length (planBytes plan).length index := by
  let a := state regs rows.flatten [] width [] source (planPayload plan).reverse
    (List.replicate index true) records []
  obtain ⟨b, hab, hb⟩ := transfer_eval (11 : Fin 15) 14 (by decide) a
  have hbe : b = state b.regs rows.flatten [] width [] source []
      (List.replicate index true) records (planPayload plan) := by
    apply state_of_stacks b regs
    rw [hb]
    funext i
    fin_cases i <;> simp [a, state, StackRoutines.transferStacks]
  rw [hbe] at hab
  let b' := state b.regs rows.flatten [] width [] source []
    (List.replicate index true) records (planPayload plan)
  obtain ⟨c, hbc, hc⟩ := readWord_eval (14 : Fin 15) 8 2
    (by decide) (by decide) (by decide) b' (planBytes plan) []
    (by simp [b',state,planPayload,planBytes]) rfl rfl
  have hce : c = state c.regs rows.flatten [] width (planBytes plan) source []
      (List.replicate index true) records [] := by
    apply state_of_stacks c regs
    rw [hc]
    funext i
    fin_cases i <;> simp [b', state]
  rw [hce] at hbc
  let c' := state c.regs rows.flatten [] width (planBytes plan) source []
    (List.replicate index true) records []
  let c0 := setData 0 false c'
  let c1 := setData 1 false c0
  let c2 := setData 2 false c1
  have hr0 := set_eval 0 false c'
  have hr1 := set_eval 1 false c0
  have hr2 := set_eval 2 false c1
  obtain ⟨ng, hng, hg⟩ := gatherCall_eval rows width plan c2.regs source
    (List.replicate index true) records (by simp [c2,c1,c0,setData])
    (by simp [c2,c1,c0,setData]) (by simp [c2,c1,c0,setData]) hrows hplan
  let d := state c2.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
    (List.replicate index true) records []
  obtain ⟨e, hde, he⟩ := copy_eval (12 : Fin 15) 14 2
    (by decide) (by decide) (by decide) d rfl
  have hee : e = state e.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
      (List.replicate index true) records (List.replicate index true) := by
    apply state_of_stacks e regs
    rw [he]
    funext i
    fin_cases i <;> simp [d, state, StackRoutines.copyStacks]
  rw [hee] at hde
  let e' := state e.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
    (List.replicate index true) records (List.replicate index true)
  obtain ⟨f, hef, hf⟩ := emitFrame_eval (14 : Fin 15) 13 2
    (by decide) (by decide) (by decide) e' rfl
  have hfe : f = state f.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
      (List.replicate index true) (Encoding.frame (List.replicate index true) ++ records) [] := by
    apply state_of_stacks f regs
    rw [hf]
    funext i
    fin_cases i <;> simp [e', state]
  rw [hfe] at hef
  let f' := state f.regs rows.flatten (GatherProgram.gathered rows plan) width [] source []
    (List.replicate index true) (Encoding.frame (List.replicate index true) ++ records) []
  obtain ⟨g, hfg, hgst⟩ := emitFrame_eval (1 : Fin 15) 13 2
    (by decide) (by decide) (by decide) f' rfl
  have hge : g = state g.regs rows.flatten [] width [] source []
      (List.replicate index true) (Encoding.frame (GatherProgram.gathered rows plan) ++
        (Encoding.frame (List.replicate index true) ++ records)) [] := by
    apply state_of_stacks g regs
    rw [hgst]
    funext i
    fin_cases i <;> simp [f', state]
  rw [hge] at hfg
  let g' := state g.regs rows.flatten [] width [] source []
    (List.replicate index true) (Encoding.frame (GatherProgram.gathered rows plan) ++
      (Encoding.frame (List.replicate index true) ++ records)) []
  let p := TupleProgram.pushedState 12 0 true g'
  let p5 := setData 5 false p
  let p6 := setData 6 true p5
  let p7 := setData 7 false p6
  have hp := TupleProgram.pushConst_eval (12 : Fin 15) (0 : Fin 8) true g'
  have hp5 := set_eval 5 false p
  have hp6 := set_eval 6 true p5
  have hp7 := set_eval 7 false p6
  have hpout : p7 = state p7.regs rows.flatten [] width [] source []
      (List.replicate (index+1) true) (Encoding.frame (GatherProgram.gathered rows plan) ++
        (Encoding.frame (List.replicate index true) ++ records)) [] := by
    apply state_of_stacks p7 regs
    funext i
    fin_cases i <;> simp [p7,p6,p5,p,g',setData,state,List.replicate_succ]
  have hrun := hab.seq (hbc.seq (hr0.seq (hr1.seq (hr2.seq
    (hg.seq (hde.seq (hef.seq (hfg.seq (hp.seq (hp5.seq (hp6.seq
      (hp7.seq (.base (.skip p7))))))))))))))
  have hcost : (3*(a.stacks 11).length+3) + ((9*(planBytes plan).length+7) +
      (1+(1+(1+(ng+((7*(d.stacks 12).length+5)+((8*(e'.stacks 14).length+8)+
      ((8*(f'.stacks 1).length+8)+(2+(1+(1+(1+0)))))))))))) =
      ng + 15*(planBytes plan).length + 15*index +
        8*(GatherProgram.gathered rows plan).length + 42 := by
    simp [a,d,e',f',state,planPayload,planBytes,Encoding.length_frame]
    ring
  rw [hcost, hpout] at hrun
  refine ⟨_,p7.regs,hrun,?_,?_,?_,?_⟩
  · simp [p7,p6,p5,setData]
  · simp [p7,p6,p5,setData]
  · simp [p7,setData]
  · let t := width.length + (planBytes plan).length + index + 1
    have ht : 1 ≤ t := by dsimp [t]; omega
    have hw : width.length ≤ t := by dsimp [t]; omega
    have hb : (planBytes plan).length ≤ t := by dsimp [t]; omega
    have hi : index ≤ t := by dsimp [t]; omega
    have hplen : plan.length ≤ (planBytes plan).length := by
      rw [planBytes, GatherProgram.encoded_plan_length]
      omega
    have hlen : (GatherProgram.gathered rows plan).length ≤ t*t := by
      rw [GatherProgram.gathered_length rows plan width.length hrows hplan]
      exact Nat.mul_le_mul (hplen.trans hb) hw
    have hgc : ng ≤ 100*t^2 := by
      apply hng.trans ((GatherProgram.traceCost_le_serialized rows width.length plan hrows hplan).trans ?_)
      change 100*(width.length+(planBytes plan).length+1)^2 ≤ 100*t^2
      gcongr
      dsimp [t]
      omega
    have ht2 : t ≤ t^2 := by nlinarith
    change ng + 15*(planBytes plan).length + 15*index +
      8*(GatherProgram.gathered rows plan).length + 42 ≤ 200*t^2
    nlinarith

@[simp] theorem labelRecords_nil (rows : List (List Bool)) (start : ℕ) :
    labelRecords rows [] start = [] := rfl

theorem labelRecords_cons (rows : List (List Bool)) (plan : List ℕ)
    (plans : List (List ℕ)) (start : ℕ) :
    labelRecords rows (plan::plans) start =
      (GatherProgram.gathered rows plan, List.replicate start true) ::
        labelRecords rows plans (start+1) := by
  simp [labelRecords, List.range'_succ]

@[simp] theorem labelRecords_length (rows : List (List Bool))
    (plans : List (List ℕ)) (start : ℕ) :
    (labelRecords rows plans start).length = plans.length := by
  simp [labelRecords]

theorem rawRecords_append (a b : List BucketProgram.Record) :
    BucketProgram.encodeRecords (a++b) =
      BucketProgram.encodeRecords a ++ BucketProgram.encodeRecords b := by
  induction a with
  | nil => rfl
  | cons a rest ih =>
      rcases a with ⟨key,value⟩
      simp only [List.cons_append, BucketProgram.encodeRecords, ih, List.append_assoc]

theorem reversed_output_cons (rows : List (List Bool)) (plan : List ℕ)
    (plans : List (List ℕ)) (start : ℕ) (records : List Bool) :
    BucketProgram.encodeRecords (labelRecords rows plans (start+1)).reverse ++
        (Encoding.frame (GatherProgram.gathered rows plan) ++
          (Encoding.frame (List.replicate start true) ++ records)) =
      BucketProgram.encodeRecords (labelRecords rows (plan::plans) start).reverse ++ records := by
  rw [labelRecords_cons, List.reverse_cons, rawRecords_append]
  simp only [BucketProgram.encodeRecords, List.append_nil, List.append_assoc]

def base (rows : List (List Bool)) (width : List Bool) (regs : Fin 8 → Bool)
    (index : ℕ) (records : List Bool) : Data :=
  state regs rows.flatten [] width [] [] [] (List.replicate index true) records []

/-- The sum of actual callback bounds and actual outer-reader overheads.
The runtime counter increases, so its current value is included explicitly. -/
def iterationCost (width : ℕ) : List (List ℕ) → ℕ → ℕ
  | [], _ => 0
  | plan::plans, start =>
      6*(planPayload plan).length + callbackCost width (planBytes plan).length start + 7 +
        iterationCost width plans (start+1)

theorem loop_eval (rows : List (List Bool)) (width : List Bool)
    (plans : List (List ℕ)) (regs : Fin 8 → Bool) (start : ℕ)
    (records suffix : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplans : ∀ plan ∈ plans, ∀ i ∈ plan, i < rows.length) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 1+iterationCost width.length plans start ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (base rows width regs start records)
          (plans.map planPayload) suffix)
        (RecordPrograms.state ports
          (base rows width rf (start+plans.length)
            (BucketProgram.encodeRecords (labelRecords rows plans start).reverse ++ records))
          false true false suffix []) := by
  induction plans generalizing regs start records with
  | nil =>
      refine ⟨1,regs,by simp [iterationCost],?_⟩
      simpa only [List.map_nil, RecordPrograms.afterTag, List.length_nil, Nat.add_zero,
        labelRecords_nil, List.reverse_nil, BucketProgram.encodeRecords, List.nil_append] using
        (Eval.while_false (body := RecordPrograms.body ports callback)
          (a := RecordPrograms.state ports (base rows width regs start records)
            false true false suffix []) (by simp))
  | cons plan plans ih =>
      let a := base rows width regs start records
      let tail := Encoding.encodeList id (plans.map planPayload) ++ suffix
      have hreader : Eval (RecordPrograms.reader ports) (6*(planPayload plan).length+4)
          (RecordPrograms.afterTag ports a ((plan::plans).map planPayload) suffix)
          (RecordPrograms.state ports a false true false tail (planPayload plan).reverse) := by
        simpa only [List.map_cons, RecordPrograms.afterTag, List.append_nil] using
          RecordPrograms.reader_eval ports a (planPayload plan) tail [] true true false
      obtain ⟨nc,rc,hc,hr5,hr6,hr7,hnc⟩ := callback_eval rows width plan
        (parserRegs regs false true false) tail records start hrows
        (hplans plan (by simp))
      let out := Encoding.frame (GatherProgram.gathered rows plan) ++
        (Encoding.frame (List.replicate start true) ++ records)
      let b := base rows width rc (start+1) out
      have hcb : Eval callback nc
          (RecordPrograms.state ports a false true false tail (planPayload plan).reverse)
          (RecordPrograms.state ports b false true false tail []) := by
        simpa only [a,b,base,parser_state,
          parserRegs_self rc false true false hr5 hr6 hr7] using hc
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports b false true false tail [])
          (RecordPrograms.afterTag ports b (plans.map planPayload) suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports b (plans.map planPayload) suffix false true
      obtain ⟨nr,rf,hnr,hr⟩ := ih rc (start+1) out
        (fun q hq => hplans q (by simp [hq]))
      have hbody := hreader.seq (hcb.seq hbranch)
      have hrun := Eval.while_true
        (show (RecordPrograms.afterTag ports a ((plan::plans).map planPayload) suffix).regs
          ports.tag = true by simp [RecordPrograms.afterTag]) hbody hr
      refine ⟨6*(planPayload plan).length+4+(nc+2)+nr+1,rf,?_,?_⟩
      · simp only [iterationCost]
        omega
      · have hindex : start+1+plans.length = start+(plan::plans).length := by simp; omega
        simpa only [RecordPrograms.loop, RecordPrograms.body, a, b, out, hindex,
          reversed_output_cons] using hrun

def traceCost (width : ℕ) (plans : List (List ℕ)) (start : ℕ) : ℕ :=
  4 + iterationCost width plans start

/-- Execute every supplied forward plan in order. The packed assignment and
row width are preserved; the raw bucket records are prepended in reverse order. -/
theorem command_eval (rows : List (List Bool)) (width : List Bool)
    (plans : List (List ℕ)) (regs : Fin 8 → Bool) (start : ℕ)
    (records suffix : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplans : ∀ plan ∈ plans, ∀ i ∈ plan, i < rows.length) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n+1 ≤ traceCost width.length plans start ∧
      Eval command n
        (state regs rows.flatten [] width []
          (ProgramEncoding.encodeRecords (plans.map planPayload) ++ suffix) []
          (List.replicate start true) records [])
        (state rf rows.flatten [] width [] suffix []
          (List.replicate (start+plans.length) true)
          (BucketProgram.encodeRecords (labelRecords rows plans start).reverse ++ records) []) := by
  let a := base rows width regs start records
  obtain ⟨n,rf,hn,he⟩ := loop_eval rows width plans regs start records suffix hrows hplans
  have hset := RecordPrograms.set_found_eval ports a (regs 5) (regs 6) (regs 7) false
    (ProgramEncoding.encodeRecords (plans.map planPayload) ++ suffix) []
  have hpop := RecordPrograms.pop_list_eval ports a (plans.map planPayload) suffix (regs 5) (regs 6)
  have hrun := hset.seq (hpop.seq he)
  refine ⟨1+(1+n),parserRegs rf false true false,by dsimp [traceCost]; omega,?_⟩
  simpa only [command,RecordPrograms.iterate,a,base,parser_state,
    parserRegs_self regs (regs 5) (regs 6) (regs 7) rfl rfl rfl] using hrun

theorem program_trace (rows : List (List Bool)) (width : List Bool)
    (plans : List (List ℕ)) (regs : Fin 8 → Bool) (start : ℕ)
    (records suffix : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplans : ∀ plan ∈ plans, ∀ i ∈ plan, i < rows.length) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ traceCost width.length plans start ∧
      Trace program n
        ((state regs rows.flatten [] width []
          (ProgramEncoding.encodeRecords (plans.map planPayload) ++ suffix) []
          (List.replicate start true) records []).withPC (some program.entry))
        ((state rf rows.flatten [] width [] suffix []
          (List.replicate (start+plans.length) true)
          (BucketProgram.encodeRecords (labelRecords rows plans start).reverse ++ records) []).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval rows width plans regs start records suffix hrows hplans
  exact ⟨n+1,rf,hn,compiled_halt_trace he 10 13⟩

theorem iterationCost_le (width : ℕ) (plans : List (List ℕ)) (start P K : ℕ)
    (hplan : ∀ plan ∈ plans, (planBytes plan).length ≤ P)
    (hindex : start+plans.length ≤ K) :
    iterationCost width plans start ≤
      plans.length * (12*P+13+200*(width+P+K+1)^2) := by
  induction plans generalizing start with
  | nil => simp [iterationCost]
  | cons plan plans ih =>
      have hp := hplan plan (by simp)
      have hs : start ≤ K := by
        simp only [List.length_cons] at hindex
        omega
      have ht := ih (start+1) (fun p hm => hplan p (by simp [hm])) (by
        simp only [List.length_cons] at hindex
        omega)
      have hc : callbackCost width (planBytes plan).length start ≤
          200*(width+P+K+1)^2 := by
        dsimp [callbackCost]
        gcongr
      have he : (planPayload plan).length ≤ 2*P+1 := by
        change (Encoding.frame (planBytes plan)).length ≤ _
        rw [Encoding.length_frame]
        omega
      simp only [iterationCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A polynomial in the number of plans, maximum serialized plan size,
row width, and initial unary index. It also covers zero-width arrays. -/
theorem traceCost_le (width : ℕ) (plans : List (List ℕ)) (start P : ℕ)
    (hp : ∀ plan ∈ plans, (planBytes plan).length ≤ P) :
    traceCost width plans start ≤
      4 + plans.length*(12*P+13+200*(width+P+start+plans.length+1)^2) := by
  have h := iterationCost_le width plans start P (start+plans.length) hp le_rfl
  dsimp [traceCost]
  simpa only [Nat.add_assoc] using Nat.add_le_add_left h 4

theorem program_primitive (rows : List (List Bool)) (width : List Bool)
    (plans : List (List ℕ)) (regs : Fin 8 → Bool) (start : ℕ)
    (records suffix : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplans : ∀ plan ∈ plans, ∀ i ∈ plan, i < rows.length) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * traceCost width.length plans start)
      (BitProgram.primitiveCfg program
        ((state regs rows.flatten [] width []
          (ProgramEncoding.encodeRecords (plans.map planPayload) ++ suffix) []
          (List.replicate start true) records []).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state rf rows.flatten [] width [] suffix []
          (List.replicate (start+plans.length) true)
          (BucketProgram.encodeRecords (labelRecords rows plans start).reverse ++ records) []).withPC none)) := by
  obtain ⟨n,rf,hn,he⟩ := program_trace rows width plans regs start records suffix hrows hplans
  exact ⟨rf,BitProgram.primitive_execution program ⟨n,hn,he⟩⟩

/-- The all-vertex producer's payloads are precisely this routine's inputs. -/
theorem alphabet_eq_planPayload (D Δ : ℕ) (scopes : List (List ℕ)) :
    SubexpPlanAlphabetBase.alphabet D Δ scopes =
      ((List.finRange D).map (fun v => IncidencePlanSpec.vertexPlan D Δ scopes v.val)).map
        planPayload := by
  rw [SubexpPlanAlphabetBase.alphabet_eq_finRange]
  simp only [List.map_map]
  rfl

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
