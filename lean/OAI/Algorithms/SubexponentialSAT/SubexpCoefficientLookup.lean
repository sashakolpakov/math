import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.SubexpRecordScan
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-!
# A fixed program for lookup in a serialized coefficient list

Every matching record is added to the accumulator. The outer list uses the
shared `encodeList id` ABI, and each body is `frame key ++ frame coefficient`.
-/

namespace SubexponentialSAT.SubexpCoefficientLookup

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 20

def frame (query source body : List Bool) : Fin 6 → List Bool :=
  ![query.reverse,source,body,[],[],[]]

def state (regs : Fin 8 → Bool) (modulus acc candidate width query source body : List Bool) : Data :=
  SubexpFlatAdd.ready regs modulus acc candidate width [] (frame query source body)

def ports : RecordPrograms.Ports 8 20 where
  tag := 0
  present := 1
  found := 7
  source := 15
  payload := 16
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def normalized (regs : Fin 8 → Bool) (v pr f : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 0 v) 1 pr) 7 f

@[simp] theorem outer_state (regs : Fin 8 → Bool)
    (modulus acc candidate width query src body : List Bool) (v pr f : Bool)
    (src' body' : List Bool) :
    RecordPrograms.state ports (state regs modulus acc candidate width query src body)
      v pr f src' body' =
      state (normalized regs v pr f) modulus acc candidate width query src' body' := by
  apply state_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [RecordPrograms.state,ports,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,
        SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,frame]

@[simp] theorem normalized_normalized (regs : Fin 8 → Bool)
    (v pr f v' pr' f' : Bool) :
    normalized (normalized regs v pr f) v' pr' f' = normalized regs v' pr' f' := by
  funext i; fin_cases i <;> simp [normalized]

@[simp] theorem normalized_self (regs : Fin 8 → Bool) :
    normalized regs (regs 0) (regs 1) (regs 7) = regs := by
  funext i; fin_cases i <;> simp [normalized]

def matcherRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def matcherPorts : Fin 6 → Fin 20 := ![16,17,14,18,19,9]

theorem matcherRegs_injective : Function.Injective matcherRegs := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 8 => x.val) h

theorem matcherPorts_injective : Function.Injective matcherPorts := by decide

abbrev matcher : Cmd 8 20 :=
  .call (ProgramLinking.liftProgram SubexpRecordScan.oneRecordProgram matcherRegs matcherPorts)

theorem matcher_eval (regs : Fin 8 → Bool)
    (modulus acc width query source key payload : List Bool) :
    ∃ n ≤ SubexpRecordScan.recordCost key query payload + 1, ∃ regs',
      Eval matcher n
        (state regs modulus acc [] width query source
          (SubexpSymbolicCost.framedRecord key payload))
        (state regs' modulus acc (if key=query then Encoding.frame payload else [])
          width query source []) ∧ regs' 4 = decide (key=query) := by
  let rr := fun i => regs (matcherRegs i)
  obtain ⟨n,hn,rr',ht,hflag⟩ := SubexpRecordScan.oneRecord_trace rr key query payload [] []
  let d := state regs modulus acc [] width query source
    (SubexpSymbolicCost.framedRecord key payload)
  let a := SubexpRecordScan.recordState rr
    (Encoding.frame key ++ (Encoding.frame payload ++ [])) [] query.reverse [] [] []
  let b := SubexpRecordScan.recordState rr' [] [] query.reverse [] []
    (if key=query then Encoding.frame payload ++ [] else [])
  let regs' := Function.extend matcherRegs rr' regs
  have ha : embedState matcherRegs matcherPorts d a = d := by
    apply embedState_eq _ _ matcherRegs_injective matcherPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;>
        simp [d,a,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,
          matcherPorts,frame,SubexpRecordScan.storage,
          SubexpSymbolicCost.framedRecord]
    · intros; rfl
    · intros; rfl
  have hb : embedState matcherRegs matcherPorts d b =
      state regs' modulus acc (if key=query then Encoding.frame payload else [])
        width query source [] := by
    apply embedState_eq _ _ matcherRegs_injective matcherPorts_injective
    · intro i
      exact matcherRegs_injective.extend_apply rr' regs i
    · intro i; fin_cases i <;>
        simp [b,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,
          matcherPorts,frame,SubexpRecordScan.storage]
    · intro j hj
      exact Function.extend_apply' _ _ _ hj
    · intro j hj
      have h9 : j ≠ 9 := fun h => hj ⟨5,by simpa [matcherPorts] using h.symm⟩
      have h16 : j ≠ 16 := fun h => hj ⟨0,by simpa [matcherPorts] using h.symm⟩
      fin_cases j <;>
        simp [d,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,SubexpFlatAdd.stacks,
          Fin.addCases,Fin.coe_ofNat_eq_mod,frame] at h9 h16 ⊢
  have he := eval_call_lifted SubexpRecordScan.oneRecordProgram matcherRegs matcherPorts d
    matcherRegs_injective matcherPorts_injective (a := a) (b := b) ht
  refine ⟨n,hn,regs',by simpa only [ha,hb,matcher] using he,?_⟩
  have h := matcherRegs_injective.extend_apply rr' regs (4 : Fin 5)
  exact h.trans hflag

def unframeRegs : Fin 2 → Fin 8 := Fin.castAdd 6
def unframePorts : Fin 2 → Fin 20 := ![9,17]

theorem unframeRegs_injective : Function.Injective unframeRegs := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 8 => x.val) h

theorem unframePorts_injective : Function.Injective unframePorts := by decide

abbrev unframeCandidate : Cmd 8 20 :=
  .call (ProgramLinking.liftProgram ParserProgram.unframeProgram unframeRegs unframePorts)

theorem unframeCandidate_eval (regs : Fin 8 → Bool)
    (modulus acc width query source payload : List Bool) :
    Eval unframeCandidate (9*payload.length+7)
      (state regs modulus acc (Encoding.frame payload) width query source [])
      (state (readRegs regs 0 1 none) modulus acc payload width query source []) := by
  let d := state regs modulus acc (Encoding.frame payload) width query source []
  let a : State 2 2 := ⟨ParserProgram.pair (regs 0) (regs 1),
    ParserProgram.pair (Encoding.frame payload ++ []) []⟩
  let b : State 2 2 := ⟨ParserProgram.pair false false,ParserProgram.pair (payload++[]) []⟩
  have ha : embedState unframeRegs unframePorts d a = d := by
    apply embedState_eq _ _ unframeRegs_injective unframePorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp [d,a,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,
        SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,frame,unframePorts,ParserProgram.pair]
    · intros; rfl
    · intros; rfl
  have hb : embedState unframeRegs unframePorts d b =
      state (readRegs regs 0 1 none) modulus acc payload width query source [] := by
    apply embedState_eq _ _ unframeRegs_injective unframePorts_injective
    · intro i; fin_cases i <;> simp [b,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,
        unframeRegs,readRegs,ParserProgram.pair]
    · intro i; fin_cases i <;> simp [b,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,
        SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,frame,unframePorts,ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0,by simpa [unframeRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1,by simpa [unframeRegs] using h.symm⟩
      simp [d,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,readRegs,h0,h1]
    · intro j hj
      have h9 : j ≠ 9 := fun h => hj ⟨0,by simpa [unframePorts] using h.symm⟩
      fin_cases j <;>
        simp [d,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,SubexpFlatAdd.stacks,
          Fin.addCases,Fin.coe_ofNat_eq_mod,frame] at h9 ⊢
  have he := eval_call_lifted ParserProgram.unframeProgram unframeRegs unframePorts d
    unframeRegs_injective unframePorts_injective (a := a) (b := b)
    (ParserProgram.unframe_trace payload [] (regs 0) (regs 1))
  simpa only [ha,hb,unframeCandidate] using he

abbrev normalize : Cmd 8 20 :=
  .seq (RecordPrograms.atom (.set 0 false))
    (.seq (RecordPrograms.atom (.set 1 true)) (RecordPrograms.atom (.set 7 false)))

theorem normalize_eval (d : Data) :
    Eval normalize 3 d ⟨normalized d.regs false true false,d.stacks⟩ := by
  have h₀ := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d)
  have h₁ := Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 8) true)
    ((StructuredProgram.Atom.set 0 false).eval d))
  have h₂ := Eval.base (StructuredProgram.Eval.atom (.set (7 : Fin 8) false)
    ((StructuredProgram.Atom.set 1 true).eval ((StructuredProgram.Atom.set 0 false).eval d)))
  simpa [normalize,RecordPrograms.atom,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,
    execInstr,normalized] using Eval.seq h₀ (Eval.seq h₁ h₂)

abbrev addCandidate : Cmd 8 20 := .seq unframeCandidate SubexpFlatAdd.coefficientAdd

abbrev callback : Cmd 8 20 :=
  .seq (.call (StackRoutines.reverseProgram 16 17 18 (0 : Fin 8) 1))
    (.seq matcher (.seq (.ite 4 addCandidate (.base .skip)) normalize))

def recordCost (B : ℕ) (query bits : List Bool) : ℕ :=
  18*bits.length + 9*query.length + 4*SubexpFlatAdd.wordCost B + 48*B + 40

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Coefficient := Quad (Word (baseWidth p μ))
abbrev Record := List Bool × Coefficient p μ

def encodeRecord (r : Record p μ) : List Bool :=
  SubexpSymbolicCost.framedRecord r.1 (SubexpFlatAdd.encode r.2)

def update (query : List Bool) (a : Coefficient p μ) (r : Record p μ) : Coefficient p μ :=
  if r.1=query then (SubexpPreparedQuartic.binaryAdd p μ M a r.2).1 else a

theorem callback_eval (regs : Fin 8 → Bool) (a : Coefficient p μ) (r : Record p μ)
    (width query source : List Bool) (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ recordCost (baseWidth p μ) query (encodeRecord p μ r), ∃ regs',
      Eval callback n
        (state regs M.bits (SubexpFlatAdd.encode a) [] width query source
          (encodeRecord p μ r).reverse)
        (state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (update p μ M query a r)) [] width query source []) := by
  let d := state regs M.bits (SubexpFlatAdd.encode a) [] width query source
    (encodeRecord p μ r).reverse
  have hrev := reverse_eval d 16 17 18 0 1 (by decide) (by decide) (by decide)
    (by decide) rfl rfl
  have he : afterReverse d 16 0 1 =
      state (readRegs regs 0 1 none) M.bits (SubexpFlatAdd.encode a) [] width query source
        (encodeRecord p μ r) := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterReverse,d,state,SubexpFlatAdd.ready,
        SubexpFlatAdd.state,SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,frame,
        StackRoutines.reverseStacks]
  have hl : (d.stacks 16).length = (encodeRecord p μ r).length := by
    simp [d,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,frame]
  rw [he,hl] at hrev
  obtain ⟨n,hn,rr,hm,hflag⟩ := matcher_eval (readRegs regs 0 1 none) M.bits
    (SubexpFlatAdd.encode a) width query source r.1 (SubexpFlatAdd.encode r.2)
  have hbound := SubexpRecordScan.recordCost_le_encoded_length r.1 query (SubexpFlatAdd.encode r.2)
  by_cases hmatch : r.1=query
  · simp only [ite_eq_left hmatch] at hm
    simp only [hmatch,decide_true] at hflag
    have hu := unframeCandidate_eval rr M.bits (SubexpFlatAdd.encode a) width query source
      (SubexpFlatAdd.encode r.2)
    obtain ⟨m,hmBound,rs,ha⟩ := SubexpFlatAdd.coefficientAdd_eval p μ M
      (readRegs rr 0 1 none) a r.2 width (frame query source []) hwidth
    have hbranch : Eval (.ite 4 addCandidate (.base .skip))
        ((9*(SubexpFlatAdd.encode r.2).length+7)+m+1)
        (state rr M.bits (SubexpFlatAdd.encode a) (Encoding.frame (SubexpFlatAdd.encode r.2))
          width query source [])
        (state rs M.bits (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a r.2).1)
          [] width query source []) :=
      Eval.ite_true hflag (Eval.seq hu ha)
    have hz := normalize_eval (state rs M.bits
      (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a r.2).1) [] width query source [])
    change Eval normalize 3
      (state rs M.bits
        (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a r.2).1)
        [] width query source [])
      (state (normalized rs false true false) M.bits
        (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a r.2).1)
        [] width query source []) at hz
    refine ⟨(9*(encodeRecord p μ r).length+7)+(n+
      (((9*(SubexpFlatAdd.encode r.2).length+7)+m+1)+3)),?_,rs,?_⟩
    · simp only [SubexpFlatAdd.encode_length] at hmBound ⊢
      unfold recordCost
      change n ≤ _ at hn
      change _ ≤ 9*(encodeRecord p μ r).length+9*query.length+19 at hbound
      omega
    · simpa only [callback,encodeRecord,update,ite_eq_left hmatch,d] using
        Eval.seq hrev (Eval.seq hm (Eval.seq hbranch hz))
  · simp only [ite_eq_right hmatch] at hm
    simp only [hmatch,decide_false] at hflag
    have hbranch : Eval (.ite 4 addCandidate (.base .skip)) 1
        (state rr M.bits (SubexpFlatAdd.encode a) [] width query source [])
        (state rr M.bits (SubexpFlatAdd.encode a) [] width query source []) :=
      Eval.ite_false hflag (Eval.base (StructuredProgram.Eval.skip _))
    have hz := normalize_eval (state rr M.bits (SubexpFlatAdd.encode a) [] width query source [])
    change Eval normalize 3
      (state rr M.bits (SubexpFlatAdd.encode a) [] width query source [])
      (state (normalized rr false true false) M.bits
        (SubexpFlatAdd.encode a) [] width query source []) at hz
    refine ⟨(9*(encodeRecord p μ r).length+7)+(n+(1+3)),?_,rr,?_⟩
    · unfold recordCost
      change _ ≤ 9*(encodeRecord p μ r).length+9*query.length+19 at hbound
      omega
    · simpa only [callback,encodeRecord,update,ite_eq_right hmatch,d] using
        Eval.seq hrev (Eval.seq hm (Eval.seq hbranch hz))

def encoded (records : List (Record p μ)) : List (List Bool) := records.map (encodeRecord p μ)

def fold (query : List Bool) (a : Coefficient p μ) (records : List (Record p μ)) :
    Coefficient p μ := records.foldl (update p μ M query) a

omit [Fact p.Prime] in
/-- Injective exponent serialization converts the actual bit comparison into
equality of the exponent indices themselves. -/
theorem fold_encoded_keys {I : Type*} [DecidableEq I] (key : I → List Bool)
    (hinj : Function.Injective key) (query : I) (a : Coefficient p μ)
    (records : List (I × Coefficient p μ)) :
    fold p μ M (key query) a (records.map (fun r => (key r.1,r.2))) =
      records.foldl (fun acc r => if r.1=query then
        (SubexpPreparedQuartic.binaryAdd p μ M acc r.2).1 else acc) a := by
  induction records generalizing a with
  | nil => rfl
  | cons r rest ih =>
      simp only [fold,List.map_cons,List.foldl_cons,update,hinj.eq_iff] at *
      exact ih _

omit [Fact p.Prime] in
theorem fold_fixedKey {D : ℕ} (query : SymbolicCost.RawIndex D) (a : Coefficient p μ)
    (records : List (SymbolicCost.RawIndex D × Coefficient p μ)) :
    fold p μ M (SubexpSymbolicCost.fixedKey query) a
        (records.map (fun r => (SubexpSymbolicCost.fixedKey r.1,r.2))) =
      records.foldl (fun acc r => if r.1=query then
        (SubexpPreparedQuartic.binaryAdd p μ M acc r.2).1 else acc) a :=
  fold_encoded_keys p μ M SubexpSymbolicCost.fixedKey SubexpSymbolicCost.fixedKey_injective
    query a records

def base (regs : Fin 8 → Bool) (a : Coefficient p μ) (width query : List Bool) : Data :=
  state regs M.bits (SubexpFlatAdd.encode a) [] width query [] []

theorem loop_eval (regs : Fin 8 → Bool) (a : Coefficient p μ)
    (records : List (Record p μ)) (width query suffix : List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ 1 + RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records),
      ∃ regs', Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (base p μ M regs a width query) (encoded p μ records) suffix)
        (RecordPrograms.state ports (base p μ M regs' (fold p μ M query a records) width query)
          false true false suffix []) := by
  induction records generalizing a regs with
  | nil =>
      refine ⟨1,by simp [encoded,RecordPrograms.budget],regs,?_⟩
      apply Eval.while_false
      simp [RecordPrograms.afterTag,encoded]
  | cons r rest ih =>
      let tail := Encoding.encodeList id (encoded p μ rest) ++ suffix
      have hreader := RecordPrograms.reader_eval ports (base p μ M regs a width query)
        (encodeRecord p μ r) tail [] true true false
      obtain ⟨n,hn,middle,hc⟩ := callback_eval p μ M (normalized regs false true false)
        a r width query tail hwidth
      have hcallback : Eval callback n
          (RecordPrograms.state ports (base p μ M regs a width query) false true false
            tail (encodeRecord p μ r).reverse)
          (RecordPrograms.state ports (base p μ M middle (update p μ M query a r) width query)
            false true false tail []) := by
        simpa only [base,outer_state] using hc
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports (base p μ M middle (update p μ M query a r) width query)
            false true false tail [])
          (RecordPrograms.afterTag ports (base p μ M middle (update p μ M query a r) width query)
            (encoded p μ rest) suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports
          (base p μ M middle (update p μ M query a r) width query) (encoded p μ rest)
          suffix false true
      have hr : Eval (RecordPrograms.reader ports) (6*(encodeRecord p μ r).length+4)
          (RecordPrograms.afterTag ports (base p μ M regs a width query)
            (encoded p μ (r::rest)) suffix)
          (RecordPrograms.state ports (base p μ M regs a width query) false true false
            tail (encodeRecord p μ r).reverse) := by
        simpa [RecordPrograms.afterTag,encoded,tail] using hreader
      have hb := Eval.seq hr (Eval.seq hcallback hbranch)
      obtain ⟨m,hm,final,hrest⟩ := ih (regs := middle) (a := update p μ M query a r)
      have hguard : (RecordPrograms.afterTag ports (base p μ M regs a width query)
          (encoded p μ (r::rest)) suffix).regs ports.tag = true := by
        simp [RecordPrograms.afterTag,encoded]
      have hrun := Eval.while_true hguard hb hrest
      refine ⟨(6*(encodeRecord p μ r).length+4+(n+2))+m+1,?_,final,?_⟩
      · simp only [encoded,List.map_cons,RecordPrograms.budget] at hm ⊢
        omega
      · simpa [RecordPrograms.loop,RecordPrograms.body,fold] using hrun

abbrev scan : Cmd 8 20 := RecordPrograms.iterate ports callback

theorem scan_eval (regs : Fin 8 → Bool) (a : Coefficient p μ)
    (records : List (Record p μ)) (width query suffix : List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ 3 + RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records),
      ∃ regs', Eval scan n
        (state regs M.bits (SubexpFlatAdd.encode a) [] width query
          (Encoding.encodeList id (encoded p μ records) ++ suffix) [])
        (state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query a records)) [] width query suffix []) := by
  obtain ⟨n,hn,regs',hl⟩ := loop_eval p μ M regs a records width query suffix hwidth
  have hs := RecordPrograms.set_found_eval ports (base p μ M regs a width query)
    (regs 0) (regs 1) (regs 7) false (Encoding.encodeList id (encoded p μ records)++suffix) []
  have hp := RecordPrograms.pop_list_eval ports (base p μ M regs a width query)
    (encoded p μ records) suffix (regs 0) (regs 1)
  refine ⟨1+(1+n),by omega,regs',?_⟩
  simpa only [scan,RecordPrograms.iterate,base,outer_state,normalized_self] using Eval.seq hs (Eval.seq hp hl)

abbrev scanProgram : Program 8 20 (StructuredCalls.size scan+1) :=
  StructuredCalls.compiled scan 15 8

theorem scan_runs (regs : Fin 8 → Bool) (a : Coefficient p μ)
    (records : List (Record p μ)) (width query suffix : List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ regs', RunsIn scanProgram
      (4+RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records))
      ((state regs M.bits (SubexpFlatAdd.encode a) [] width query
          (Encoding.encodeList id (encoded p μ records)++suffix) []).withPC (some scanProgram.entry))
      ((state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query a records)) [] width query suffix []).withPC none) := by
  obtain ⟨n,hn,regs',h⟩ := scan_eval p μ M regs a records width query suffix hwidth
  exact ⟨regs',n+1,by omega,StructuredCalls.compiled_halt_trace h 15 8⟩

theorem scan_primitive_runs (regs : Fin 8 → Bool) (a : Coefficient p μ)
    (records : List (Record p μ)) (width query suffix : List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive scanProgram).step
      (BitProgram.primitiveOverhead scanProgram *
        (4+RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records)))
      (BitProgram.primitiveCfg scanProgram
        ((state regs M.bits (SubexpFlatAdd.encode a) [] width query
          (Encoding.encodeList id (encoded p μ records)++suffix) []).withPC (some scanProgram.entry)))
      (BitProgram.primitiveCfg scanProgram
        ((state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query a records)) [] width query suffix []).withPC none)) := by
  obtain ⟨regs',h⟩ := scan_runs p μ M regs a records width query suffix hwidth
  exact ⟨regs',BitProgram.primitive_execution _ h⟩

def zeroCoefficient : Coefficient p μ :=
  let z := SubexpPreparedQuartic.zeroWord p μ
  ⟨z,z,z,z⟩

omit [Fact p.Prime] in
theorem encode_zero : SubexpFlatAdd.encode (zeroCoefficient p μ) =
    List.replicate (4*baseWidth p μ) false := by
  have hB : 4*baseWidth p μ =
      baseWidth p μ+(baseWidth p μ+(baseWidth p μ+baseWidth p μ)) := by omega
  change List.replicate (baseWidth p μ) false ++
      (List.replicate (baseWidth p μ) false ++
        (List.replicate (baseWidth p μ) false ++
          (List.replicate (baseWidth p μ) false ++ []))) =
    List.replicate (4*baseWidth p μ) false
  rw [hB,List.replicate_add,List.replicate_add,List.replicate_add]
  simp only [List.append_nil]

abbrev «initialize» : Cmd 8 20 :=
  .seq (.call (StackRoutines.copyProgram 10 11 12 (0 : Fin 8) 1))
    (.call (zeroFillProgram 11 8 (0 : Fin 8) 1))

omit [Fact p.Prime] in
theorem initialize_eval (regs : Fin 8 → Bool) (width query source : List Bool)
    (hwidth : width.length = baseWidth p μ) :
    Eval «initialize» (14*baseWidth p μ+8)
      (state regs M.bits [] [] width query source [])
      (state (readRegs regs 0 1 none) M.bits (SubexpFlatAdd.encode (zeroCoefficient p μ)) []
        width query source []) := by
  let d := state regs M.bits [] [] width query source []
  have hc := copy_eval d 10 11 12 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  let d₁ := afterCopy d 10 11 0 1
  have hz := zeroFill_eval 11 8 0 1 (by decide) (by decide) d₁
  have hl : (d.stacks 10).length = baseWidth p μ := hwidth
  have hl₁ : (d₁.stacks 11).length = baseWidth p μ := by
    simpa [d₁,d,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,
      afterCopy,StackRoutines.copyStacks] using hwidth
  have he : (⟨readRegs d₁.regs 0 1 none,
      zeroFillStacks 11 8 (d₁.stacks 11).length d₁.stacks⟩ : Data) =
      state (readRegs regs 0 1 none) M.bits (SubexpFlatAdd.encode (zeroCoefficient p μ)) []
        width query source [] := by
    apply state_ext
    · simp [d₁,d,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,afterCopy,StackRoutines.readRegs_reset]
    · rw [hl₁,encode_zero]
      funext i; fin_cases i <;>
        simp [d₁,d,state,SubexpFlatAdd.ready,SubexpFlatAdd.state,SubexpFlatAdd.stacks,Fin.addCases,Fin.coe_ofNat_eq_mod,
          frame,afterCopy,StackRoutines.copyStacks,zeroFillStacks]
  have h := Eval.seq hc hz
  rw [he] at h
  simpa only [hl,hl₁,show (7*baseWidth p μ+5)+(7*baseWidth p μ+3)=14*baseWidth p μ+8 by omega,
    «initialize»] using h

abbrev lookup : Cmd 8 20 := .seq «initialize» scan

abbrev lookupProgram : Program 8 20 (StructuredCalls.size lookup+1) :=
  StructuredCalls.compiled lookup 15 8

theorem scan_control_size : StructuredCalls.size scan = 798 := by decide
theorem lookup_control_size : StructuredCalls.size lookup = 814 := by decide

theorem lookup_eval (regs : Fin 8 → Bool) (records : List (Record p μ))
    (width query suffix : List Bool) (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ 14*baseWidth p μ+11+
        RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records),
      ∃ regs', Eval lookup n
        (state regs M.bits [] [] width query
          (Encoding.encodeList id (encoded p μ records)++suffix) [])
        (state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query (zeroCoefficient p μ) records)) []
          width query suffix []) := by
  have hi := initialize_eval p μ M regs width query
    (Encoding.encodeList id (encoded p μ records)++suffix) hwidth
  obtain ⟨n,hn,regs',hs⟩ := scan_eval p μ M (readRegs regs 0 1 none) (zeroCoefficient p μ)
    records width query suffix hwidth
  exact ⟨14*baseWidth p μ+8+n,by omega,regs',Eval.seq hi hs⟩

theorem lookup_runs (regs : Fin 8 → Bool) (records : List (Record p μ))
    (width query suffix : List Bool) (hwidth : width.length = baseWidth p μ) :
    ∃ regs', RunsIn lookupProgram
      (14*baseWidth p μ+12+
        RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records))
      ((state regs M.bits [] [] width query
          (Encoding.encodeList id (encoded p μ records)++suffix) []).withPC (some lookupProgram.entry))
      ((state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query (zeroCoefficient p μ) records)) []
          width query suffix []).withPC none) := by
  obtain ⟨n,hn,regs',h⟩ := lookup_eval p μ M regs records width query suffix hwidth
  exact ⟨regs',n+1,by omega,StructuredCalls.compiled_halt_trace h 15 8⟩

theorem lookup_primitive_runs (regs : Fin 8 → Bool) (records : List (Record p μ))
    (width query suffix : List Bool) (hwidth : width.length = baseWidth p μ) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive lookupProgram).step
      (BitProgram.primitiveOverhead lookupProgram *
        (14*baseWidth p μ+12+
          RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records)))
      (BitProgram.primitiveCfg lookupProgram
        ((state regs M.bits [] [] width query
          (Encoding.encodeList id (encoded p μ records)++suffix) []).withPC (some lookupProgram.entry)))
      (BitProgram.primitiveCfg lookupProgram
        ((state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query (zeroCoefficient p μ) records)) []
          width query suffix []).withPC none)) := by
  obtain ⟨regs',h⟩ := lookup_runs p μ M regs records width query suffix hwidth
  exact ⟨regs',BitProgram.primitive_execution _ h⟩

/-- The same concrete lookup executes inside arbitrary caller storage. Ports
outside the supplied injective maps retain their exact original contents. -/
theorem lookup_runs_lifted {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 20 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (ambient : Cfg R S (StructuredCalls.size lookup+1))
    (regs : Fin 8 → Bool) (records : List (Record p μ))
    (width query suffix : List Bool) (hwidth : width.length = baseWidth p μ) :
    ∃ regs', RunsIn (ProgramLinking.liftProgram lookupProgram register stack)
      (14*baseWidth p μ+12+
        RecordPrograms.budget (recordCost (baseWidth p μ) query) (encoded p μ records))
      (ProgramLinking.embedCfg register stack id none ambient
        ((state regs M.bits [] [] width query
          (Encoding.encodeList id (encoded p μ records)++suffix) []).withPC (some lookupProgram.entry)))
      (ProgramLinking.embedCfg register stack id none ambient
        ((state (normalized regs' false true false) M.bits
          (SubexpFlatAdd.encode (fold p μ M query (zeroCoefficient p μ) records)) []
          width query suffix []).withPC none)) := by
  obtain ⟨regs',h⟩ := lookup_runs p μ M regs records width query suffix hwidth
  exact ⟨regs',ProgramLinking.liftProgram_runsIn lookupProgram register stack ambient hr hs h⟩

/-- The measured loop bound is polynomial in the serialized data and runtime
word width; the finite instruction table is independent of all three. -/
theorem scan_budget_le_input (B : ℕ) (query : List Bool) (records : List (List Bool)) :
    4+RecordPrograms.budget (recordCost B query) records ≤
      (9*query.length+4*SubexpFlatAdd.wordCost B+48*B+75)*
        ((Encoding.encodeList id records).length+1) := by
  have h := RecordPrograms.program_budget_le_input (recordCost B query) records 18
    (9*query.length+4*SubexpFlatAdd.wordCost B+48*B+40)
    (by intro bits hb; unfold recordCost; omega)
  have he : 18+(9*query.length+4*SubexpFlatAdd.wordCost B+48*B+40)+17 =
      9*query.length+4*SubexpFlatAdd.wordCost B+48*B+75 := by omega
  simpa only [he,ProgramEncoding.encodeRecords] using h

theorem fold_quotient (c : Fin 4 → ZMod (p^μ)) (query : List Bool)
    (a : Coefficient p μ) (records : List (Record p μ)) :
    quotientDenote c ((fold p μ M query a records).map (wordValue p μ)) =
      quotientDenote c (a.map (wordValue p μ)) +
        (records.map (fun r => if r.1=query then
          quotientDenote c (r.2.map (wordValue p μ)) else 0)).sum := by
  induction records generalizing a with
  | nil => simp [fold]
  | cons r rest ih =>
      simp only [fold,List.foldl_cons] at *
      rw [ih]
      by_cases he : r.1=query
      · simp only [update,he,ite_true,SubexpPreparedQuartic.binaryAdd_quotient,
          List.map_cons,List.sum_cons]
        exact add_assoc _ _ _
      · simp only [update,he,ite_false,List.map_cons,List.sum_cons,zero_add]

omit [Fact p.Prime] in
theorem zero_quotient (c : Fin 4 → ZMod (p^μ)) :
    quotientDenote c ((zeroCoefficient p μ).map (wordValue p μ)) = 0 := by
  simp only [zeroCoefficient,Quad.map,SubexpPreparedQuartic.zeroWord_value,
    quotientDenote_const,map_zero]

/-- In particular, the zero-initialized lookup returns the sum of every
coefficient stored under the requested key, including duplicate keys. -/
theorem lookup_quotient (c : Fin 4 → ZMod (p^μ)) (query : List Bool)
    (records : List (Record p μ)) :
    quotientDenote c ((fold p μ M query (zeroCoefficient p μ) records).map (wordValue p μ)) =
      (records.map (fun r => if r.1=query then
        quotientDenote c (r.2.map (wordValue p μ)) else 0)).sum := by
  rw [fold_quotient,zero_quotient,zero_add]

end SubexponentialSAT.SubexpCoefficientLookup

end OAI.Algorithms
