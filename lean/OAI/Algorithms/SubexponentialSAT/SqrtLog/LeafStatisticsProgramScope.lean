import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramLookup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramRecords
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup

namespace OAI.Algorithms

/-! Count precisely the unpinned identifiers in an explicit scope. The mask is
in original coordinate order and the framed natural identifiers are read at
runtime. No arity or other statistic is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 7 7
abbrev Code := Cmd 7 7
abbrev unary (n : ℕ) := List.replicate n true

def state (r : Fin 7 → Bool) (mask index scan tmp acc source payload : List Bool) : Data :=
  ⟨r, ![mask,index,scan,tmp,acc,source,payload]⟩
def ports : RecordPrograms.Ports 7 7 :=
  ⟨4,5,6,5,6,by decide,by decide,by decide,by decide⟩
def parserRegs (r : Fin 7 → Bool) (t p f : Bool) :=
  Function.update (Function.update (Function.update r 4 t) 5 p) 6 f

theorem parser_state (r : Fin 7 → Bool) (mask acc source payload src pay : List Bool)
    (t p f : Bool) :
    RecordPrograms.state ports (state r mask [] [] [] acc source payload) t p f src pay =
      state (parserRegs r t p f) mask [] [] [] acc src pay := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> rfl

def lookupRegs : Fin 4 → Fin 7 := Fin.castAdd 3
def lookupStacks : Fin 5 → Fin 7 := Fin.castAdd 2
theorem lookupRegs_injective : Function.Injective lookupRegs := Fin.castAdd_injective _ _
theorem lookupStacks_injective : Function.Injective lookupStacks := Fin.castAdd_injective _ _
def lookup : Code := .call (ProgramLinking.liftProgram Lookup.program lookupRegs lookupStacks)

theorem lookup_eval (r : Fin 7 → Bool) (mask : List Bool) (v : ℕ) (hv : v < mask.length)
    (acc source : List Bool) :
    ∃ n rf, n ≤ 12*mask.length+12 ∧ rf 2 = mask[v] ∧
      (∀ i : Fin 7, 4 ≤ i.val → rf i = r i) ∧
      Eval lookup n (state r mask (unary v) [] [] acc source [])
        (state rf mask [] [] [] acc source []) := by
  let before := mask.take v
  let after := mask.drop (v+1)
  have hlen : before.length = v := by simp [before,Nat.min_eq_left hv.le]
  have hsplit : before ++ mask[v]::after = mask := by
    have h := List.take_append_drop v mask
    rw [List.drop_eq_getElem_cons hv] at h
    exact h
  obtain ⟨rs,hbit,n,hn,ht⟩ := Lookup.program_runsIn (r ∘ lookupRegs) before after acc mask[v]
  let a := state r mask (unary v) [] [] acc source []
  let b := Lookup.state rs mask [] [] [] acc
  have hp : projectState lookupRegs lookupStacks a =
      Lookup.state (r ∘ lookupRegs) (before ++ mask[v]::after) (unary before.length) [] [] acc := by
    rw [hsplit,hlen]
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [← hp,hsplit] at ht
  have he := eval_call_from_state Lookup.program lookupRegs lookupStacks a
    lookupRegs_injective lookupStacks_injective (b := b) ht
  let e := embedState lookupRegs lookupStacks a b
  have heq : e = state e.regs mask [] [] [] acc source [] := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 0
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 1
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 2
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 3
    · exact embedState_stack lookupRegs lookupStacks a b lookupStacks_injective 4
    · exact embedState_stack_frame lookupRegs lookupStacks a b _ (by decide)
    · exact embedState_stack_frame lookupRegs lookupStacks a b _ (by decide)
  refine ⟨n,e.regs,?_,?_,?_,?_⟩
  · have hm : before.length + 1 + after.length = mask.length := by
      have := congrArg List.length hsplit
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using this
    simpa [hm] using hn
  · exact (embedState_register lookupRegs lookupStacks a b lookupRegs_injective 2).trans hbit
  · intro i hi
    exact embedState_register_frame lookupRegs lookupStacks a b i (by
      rintro ⟨j,hj⟩
      have he : j.val = i.val := congrArg Fin.val hj
      have hlt := j.isLt
      omega)
  · change Eval lookup n a e at he
    rw [heq] at he
    exact he

def dropTag : Code := .base (.atom (.pop 6 0 1))
def transfer : Code := .call (StackRoutines.transferProgram 6 1 0 1)
def increment : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 4 0)))
def choose : Code := .ite 2 (.base .skip) increment
def callback : Code := .seq dropTag (.seq transfer (.seq lookup choose))

theorem callback_eval (r : Fin 7 → Bool) (mask : List Bool) (v : ℕ)
    (hv : v < mask.length) (acc source : List Bool) :
    ∃ n rf, n ≤ 16*(mask.length+1) ∧
      (∀ i : Fin 7, 4 ≤ i.val → rf i = r i) ∧
      Eval callback n (state r mask [] [] [] acc source (Encoding.encodeNat v).reverse)
        (state rf mask [] [] [] (if mask[v] then acc else true::acc) source []) := by
  let r1 := readRegs r 0 1 (some false)
  let r2 := readRegs r1 0 1 none
  have hdrop : Eval dropTag 1
      (state r mask [] [] [] acc source (Encoding.encodeNat v).reverse)
      (state r1 mask [] [] [] acc source (unary v)) := by
    have h := Eval.base (StructuredProgram.Eval.atom (.pop (6 : Fin 7) 0 1)
      (state r mask [] [] [] acc source (Encoding.encodeNat v).reverse))
    convert h using 1
    · rfl
    · apply congrArg₂ StructuredProgram.State.mk
      · funext i
        fin_cases i <;> simp [r1, state, Encoding.encodeNat, List.reverse_append,
          List.reverse_replicate,
          StructuredProgram.Atom.instr, execInstr]
      · funext i
        fin_cases i <;> simp [state, unary, Encoding.encodeNat, List.reverse_append,
          List.reverse_replicate, StructuredProgram.Atom.instr, execInstr]
  have htransfer : Eval transfer (3*v+3)
      (state r1 mask [] [] [] acc source (unary v))
      (state r2 mask (unary v) [] [] acc source []) := by
    apply Eval.call
    convert (ListRegisterProgram.transfer_run (6 : Fin 7) 1 (0 : Fin 7) 1
      (by decide) (by decide) r1 (state r1 mask [] [] [] acc source (unary v)).stacks) using 1 <;>
      simp [r2,state,unary,StackRoutines.transferStacks,List.reverse_replicate]
    funext i; fin_cases i <;> rfl
  obtain ⟨nl,rl,hnl,hbit,hframe,hl⟩ := lookup_eval r2 mask v hv acc source
  let a := state rl mask [] [] [] acc source []
  have hchoose : ∃ nc rf, nc ≤ 3 ∧ (∀ i : Fin 7, 4 ≤ i.val → rf i = rl i) ∧
      Eval choose nc a (state rf mask [] [] [] (if mask[v] then acc else true::acc) source []) := by
    cases hb : mask[v] with
    | true =>
      refine ⟨1,rl,by omega,fun i hi => rfl,?_⟩
      apply Eval.ite_true
      · change rl 2 = true
        simpa only [hb] using hbit
      · exact Eval.base (StructuredProgram.Eval.skip a)
    | false =>
      let rf := Function.update rl 0 true
      refine ⟨3,rf,by omega,?_,?_⟩
      · intro i hi
        have h0 : i ≠ 0 := by intro h; subst i; contradiction
        simp [rf,h0]
      · apply Eval.ite_false (by
          change rl 2 = false
          simpa only [hb] using hbit)
        have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 7) true) a)).seq
          (Eval.base (StructuredProgram.Eval.atom (.push (4 : Fin 7) 0) _))
        convert h using 1
        · rfl
        · apply congrArg (StructuredProgram.State.mk _)
          funext i
          fin_cases i <;>
            simp [a,state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg,execInstr]
  obtain ⟨nc,rf,hnc,hrf,hc⟩ := hchoose
  refine ⟨1+(3*v+3)+(nl+nc),rf,by omega,?_,?_⟩
  · intro i hi
    rw [hrf i hi,hframe i hi]
    have h0 : i ≠ 0 := by intro h; subst i; contradiction
    have h1 : i ≠ 1 := by intro h; subst i; contradiction
    simp [r2,r1,readRegs,h0,h1]
  · have h := hdrop.seq (htransfer.seq (hl.seq hc))
    simpa only [callback, Nat.add_assoc] using h

noncomputable def decoded (bits : List Bool) : ℕ := by
  classical
  exact if h : ∃ v, Encoding.encodeNat v = bits then Classical.choose h else 0
@[simp] theorem decoded_encode (v : ℕ) : decoded (Encoding.encodeNat v) = v := by
  classical
  unfold decoded
  split
  · rename_i h
    exact Encoding.encodeNat_injective (Classical.choose_spec h)
  · rename_i h
    exact (h ⟨v,rfl⟩).elim

noncomputable def update (mask bits acc : List Bool) :=
  if low mask (decoded bits) then true::acc else acc

def invariant (mask : List Bool) (d : Data) : Prop :=
  ∃ r acc, d = state r mask [] [] [] acc [] []
def read (d : Data) := d.stacks 4

theorem callback_contract (mask : List Bool) :
    LeafProgram.FoldContract ports callback read (update mask)
      (fun _ => 16*(mask.length+1)) (invariant mask)
      (fun bits => ∃ v, v < mask.length ∧ Encoding.encodeNat v = bits) := by
  rintro bits tail base ⟨v,hv,rfl⟩ ⟨r,acc,rfl⟩
  obtain ⟨n,rf,hn,hframe,he⟩ := callback_eval (parserRegs r false true false) mask v hv acc tail
  have h4 : rf 4 = false := by simpa [parserRegs] using hframe 4 (by decide)
  have h5 : rf 5 = true := by simpa [parserRegs] using hframe 5 (by decide)
  have h6 : rf 6 = false := by simpa [parserRegs] using hframe 6 (by decide)
  have hreset : parserRegs rf false true false = rf := by
    funext i; fin_cases i <;> simp [parserRegs,h4,h5,h6]
  refine ⟨n,state rf mask [] [] [] (if mask[v] then acc else true::acc) [] [],hn,
    ⟨rf,_,rfl⟩,?_,?_⟩
  · cases hb : mask[v] <;>
      simp [LeafProgram.foldEffect,read,update,low,List.getElem?_eq_getElem hv,state,hb]
  · rw [parser_state,parser_state,hreset]
    exact he

def command := LeafProgram.foldCommand ports callback
def program := LeafProgram.foldProgram ports callback

theorem fold_update (mask : List Bool) (scope : List ℕ) (acc : List Bool) :
    (scope.map Encoding.encodeNat).foldl (fun a b => update mask b a) acc =
      unary (scope.filter (low mask)).length ++ acc := by
  induction scope generalizing acc with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ih]
    simp only [update,decoded_encode]
    by_cases h : low mask v = true
    · simp [h,unary,List.replicate_succ',List.append_assoc]
    · simp [h,unary]

theorem program_runsIn (r : Fin 7 → Bool) (mask : List Bool) (scope : List ℕ)
    (hv : ∀ v ∈ scope, v < mask.length) :
    ∃ rf, RunsIn program
      (4 + RecordPrograms.budget (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat))
      ((RecordPrograms.state ports (state r mask [] [] [] [] [] []) false true false
        (Encoding.encodeList Encoding.encodeNat scope) []).withPC (some program.entry))
      ((state rf mask [] [] [] (unary (scope.filter (low mask)).length) [] []).withPC none) := by
  obtain ⟨next,hn,hvout,he⟩ := LeafProgram.foldProgram_run ports callback read (update mask)
    (fun _ => 16*(mask.length+1)) (invariant mask)
    (fun bits => ∃ v, v < mask.length ∧ Encoding.encodeNat v = bits)
    (callback_contract mask) (scope.map Encoding.encodeNat) []
    (state r mask [] [] [] [] [] [])
    (by intro bits hb; obtain ⟨v,hv0,rfl⟩ := List.mem_map.mp hb; exact ⟨v,hv v hv0,rfl⟩)
    ⟨r,[],rfl⟩ false true false
  obtain ⟨rf,acc,rfl⟩ := hn
  have hacc : acc = unary (scope.filter (low mask)).length := by
    simpa [read,state,fold_update] using hvout
  subst acc
  refine ⟨parserRegs rf false true false,?_⟩
  simpa only [List.append_nil,parser_state,SubexpScopeCountSetup.encode_scope,program] using he

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope

end OAI.Algorithms
