import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramScope
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramMax
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 10 12
abbrev Code := Cmd 10 12
abbrev unary (n : ℕ) := List.replicate n true

def state (r : Fin 10 → Bool) (mask current source payload : List Bool) (a q : ℕ) : Data :=
  ⟨r, ![mask,[],[],[],[],current,[],source,payload,unary a,[],unary q]⟩
def ports : RecordPrograms.Ports 10 12 :=
  ⟨7,8,9,7,8,by decide,by decide,by decide,by decide⟩
def parserRegs (r : Fin 10 → Bool) (t p f : Bool) :=
  Function.update (Function.update (Function.update r 7 t) 8 p) 9 f

theorem parser_state (r : Fin 10 → Bool) (mask current source payload src pay : List Bool)
    (a q : ℕ) (t p f : Bool) :
    RecordPrograms.state ports (state r mask current source payload a q) t p f src pay =
      state (parserRegs r t p f) mask current src pay a q := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> rfl

def scopeRegs : Fin 7 → Fin 10 := Fin.castAdd 3
def scopeStacks : Fin 7 → Fin 12 := Fin.castAdd 5
theorem scopeRegs_injective : Function.Injective scopeRegs := Fin.castAdd_injective _ _
theorem scopeStacks_injective : Function.Injective scopeStacks := Fin.castAdd_injective _ _
def scopeCall : Code := .call (ProgramLinking.liftProgram Scope.program scopeRegs scopeStacks)
def prepare : Code := .base (SubexpParameterProgram.atoms [.set 4 false,.set 5 true,.set 6 false])
def prepared (r : Fin 10 → Bool) := Function.update (Function.update (Function.update r 4 false) 5 true) 6 false

theorem prepare_eval (d : Data) : Eval prepare 3 d ⟨prepared d.regs,d.stacks⟩ := by
  exact .base (SubexpParameterProgram.atoms_eval _ d)

theorem scopeCall_eval (r : Fin 10 → Bool) (mask source : List Bool) (scope : List ℕ)
    (hv : ∀ v ∈ scope, v < mask.length) (a q : ℕ) :
    ∃ n rf, n ≤ 4+RecordPrograms.budget (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = r i) ∧
      Eval scopeCall n (state (prepared r) mask (Encoding.encodeList Encoding.encodeNat scope) source [] a q)
        ⟨rf,Function.update (state r mask [] source [] a q).stacks 4
          (unary (scope.filter (Scope.low mask)).length)⟩ := by
  let d := state (prepared r) mask (Encoding.encodeList Encoding.encodeNat scope) source [] a q
  obtain ⟨rr,nt,hnt,ht⟩ := Scope.program_runsIn (r ∘ scopeRegs) mask scope hv
  let b := Scope.state rr mask [] [] [] (unary (scope.filter (Scope.low mask)).length) [] []
  have hp : projectState scopeRegs scopeStacks d =
      RecordPrograms.state Scope.ports (Scope.state (r ∘ scopeRegs) mask [] [] [] [] [] [])
        false true false (Encoding.encodeList Encoding.encodeNat scope) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [←hp] at ht
  have he := eval_call_from_state Scope.program scopeRegs scopeStacks d scopeRegs_injective scopeStacks_injective ht
  let e := embedState scopeRegs scopeStacks d b
  have heq : e = ⟨e.regs,Function.update (state r mask [] source [] a q).stacks 4
      (unary (scope.filter (Scope.low mask)).length)⟩ := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i
    all_goals first
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 0
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 1
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 2
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 3
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 4
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 5
      | exact embedState_stack scopeRegs scopeStacks d b scopeStacks_injective 6
      | exact embedState_stack_frame scopeRegs scopeStacks d b _ (by decide)
  refine ⟨nt,e.regs,hnt,?_,?_⟩
  · intro i hi
    have h := embedState_register_frame scopeRegs scopeStacks d b i (by
      rintro ⟨j,hj⟩
      have he : j.val = i.val := congrArg Fin.val hj
      have hlt := j.isLt
      omega)
    have h4 : i ≠ 4 := by intro he; subst i; contradiction
    have h5 : i ≠ 5 := by intro he; subst i; contradiction
    have h6 : i ≠ 6 := by intro he; subst i; contradiction
    simpa [e, d,state,prepared,h4,h5,h6] using h
  · change Eval scopeCall nt d e at he
    rw [heq] at he
    exact he

def maxRegs : Fin 3 → Fin 10 := Fin.castAdd 7
def maxStacks : Fin 3 → Fin 12 := ![4,9,10]
theorem maxRegs_injective : Function.Injective maxRegs := Fin.castAdd_injective _ _
theorem maxStacks_injective : Function.Injective maxStacks := by decide

def maxCall : Code := .call (ProgramLinking.liftProgram Max.program maxRegs maxStacks)

theorem maxCall_eval (r : Fin 10 → Bool) (mask source : List Bool) (x a q : ℕ) :
    ∃ rf, (∀ i : Fin 10, 3 ≤ i.val → rf i = r i) ∧
      Eval maxCall (8*x+6)
        ⟨r,Function.update (state r mask [] source [] a q).stacks 4 (unary x)⟩
        (state rf mask [] source [] (max x a) q) := by
  let d : Data := ⟨r,Function.update (state r mask [] source [] a q).stacks 4 (unary x)⟩
  obtain ⟨rr,hr⟩ := Max.command_eval (r ∘ maxRegs) x a
  let b := Max.state rr [] (unary (max x a)) []
  have hp : projectState maxRegs maxStacks d = Max.state (r ∘ maxRegs) (unary x) (unary a) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  have ht := compiled_halt_trace hr 0 1
  rw [←hp] at ht
  have he := eval_call_from_state Max.program maxRegs maxStacks d maxRegs_injective maxStacks_injective ht
  let e := embedState maxRegs maxStacks d b
  have heq : e = state e.regs mask [] source [] (max x a) q := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i
    all_goals first
      | exact embedState_stack maxRegs maxStacks d b maxStacks_injective 0
      | exact embedState_stack maxRegs maxStacks d b maxStacks_injective 1
      | exact embedState_stack maxRegs maxStacks d b maxStacks_injective 2
      | exact embedState_stack_frame maxRegs maxStacks d b _ (by decide)
  refine ⟨e.regs,?_,?_⟩
  · intro i hi
    exact embedState_register_frame maxRegs maxStacks d b i (by
      rintro ⟨j,hj⟩
      have he : j.val = i.val := congrArg Fin.val hj
      have hlt := j.isLt
      omega)
  · change Eval maxCall (8*x+5+1) d e at he
    rw [heq] at he
    convert he using 1

def transfer : Code := .call (StackRoutines.transferProgram 8 5 0 1)
def increment : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 11 0)))
def callback : Code := .seq transfer (.seq prepare (.seq scopeCall (.seq maxCall increment)))

def scopeBudget (mask : List Bool) (scope : List ℕ) :=
  4+RecordPrograms.budget (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat)

theorem callback_eval (r : Fin 10 → Bool) (mask source : List Bool) (scope : List ℕ)
    (hv : ∀ v ∈ scope, v < mask.length) (a q : ℕ) :
    ∃ n rf, n ≤ 3*(Encoding.encodeList Encoding.encodeNat scope).length+
        scopeBudget mask scope+8*scope.length+14 ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = r i) ∧
      Eval callback n
        (state r mask [] source (Encoding.encodeList Encoding.encodeNat scope).reverse a q)
        (state rf mask [] source [] (max (scope.filter (Scope.low mask)).length a) (q+1)) := by
  let bits := Encoding.encodeList Encoding.encodeNat scope
  let r1 := readRegs r 0 1 none
  have htransfer : Eval transfer (3*bits.length+3)
      (state r mask [] source bits.reverse a q)
      (state r1 mask bits source [] a q) := by
    apply Eval.call
    convert (ListRegisterProgram.transfer_run (8 : Fin 12) 5 (0 : Fin 10) 1
      (by decide) (by decide) r (state r mask [] source bits.reverse a q).stacks) using 1 <;>
      simp [r1,state,StackRoutines.transferStacks]
    funext i; fin_cases i <;> rfl
  have hp := prepare_eval (state r1 mask bits source [] a q)
  obtain ⟨ns,rs,hns,hrs,hs⟩ := scopeCall_eval r1 mask source scope hv a q
  obtain ⟨rm,hrm,hm⟩ := maxCall_eval rs mask source (scope.filter (Scope.low mask)).length a q
  let rf := Function.update rm 0 true
  have hi : Eval increment 2
      (state rm mask [] source [] (max (scope.filter (Scope.low mask)).length a) q)
      (state rf mask [] source [] (max (scope.filter (Scope.low mask)).length a) (q+1)) := by
    have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) true)
      (state rm mask [] source [] (max (scope.filter (Scope.low mask)).length a) q))).seq
      (Eval.base (StructuredProgram.Eval.atom (.push (11 : Fin 12) 0) _))
    convert h using 1
    · rfl
    · apply congrArg (StructuredProgram.State.mk _)
      funext i; fin_cases i <;>
        simp [state,unary,List.replicate_succ,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
execInstr]
  refine ⟨_,rf,?_,?_,htransfer.seq (hp.seq (hs.seq (hm.seq hi)))⟩
  · have hlen := List.length_filter_le (Scope.low mask) scope
    dsimp [scopeBudget,bits] at *
    omega
  · intro i hi
    have h0 : i ≠ 0 := by intro he; subst i; contradiction
    have h1 : i ≠ 1 := by intro he; subst i; contradiction
    simp only [rf,Function.update_of_ne h0]
    rw [hrm i (by omega),hrs i hi]
    simp [r1,readRegs,h0,h1]

noncomputable def decoded (bits : List Bool) : List ℕ := by
  classical
  exact if h : ∃ scope, Encoding.encodeList Encoding.encodeNat scope = bits then Classical.choose h else []
@[simp] theorem decoded_encode (scope : List ℕ) :
    decoded (Encoding.encodeList Encoding.encodeNat scope) = scope := by
  classical
  unfold decoded
  split
  · rename_i h
    exact Encoding.encodeList_injective Encoding.encodeNat_injective (Classical.choose_spec h)
  · rename_i h
    exact (h ⟨scope,rfl⟩).elim

noncomputable def cost (mask bits : List Bool) :=
  3*bits.length+scopeBudget mask (decoded bits)+8*(decoded bits).length+14
noncomputable def update (mask bits : List Bool) (t : ℕ × ℕ) : ℕ × ℕ :=
  (max ((decoded bits).filter (Scope.low mask)).length t.1,t.2+1)

def invariant (mask : List Bool) (d : Data) : Prop :=
  ∃ r a q, d = state r mask [] [] [] a q
noncomputable def unaryValue (bits : List Bool) : ℕ := bits.length
def read (d : Data) : ℕ × ℕ := ((d.stacks 9).length,(d.stacks 11).length)

theorem callback_contract (mask : List Bool) :
    LeafProgram.FoldContract ports callback read (update mask) (cost mask) (invariant mask)
      (fun bits => ∃ scope, (∀ v ∈ scope, v < mask.length) ∧
        Encoding.encodeList Encoding.encodeNat scope = bits) := by
  rintro bits tail base ⟨scope,hv,rfl⟩ ⟨r,a,q,rfl⟩
  obtain ⟨n,rf,hn,hr,he⟩ := callback_eval (parserRegs r false true false) mask tail scope hv a q
  have h7 : rf 7 = false := by simpa [parserRegs] using hr 7 (by decide)
  have h8 : rf 8 = true := by simpa [parserRegs] using hr 8 (by decide)
  have h9 : rf 9 = false := by simpa [parserRegs] using hr 9 (by decide)
  have hreset : parserRegs rf false true false = rf := by
    funext i; fin_cases i <;> simp [parserRegs,h7,h8,h9]
  refine ⟨n,state rf mask [] [] [] (max (scope.filter (Scope.low mask)).length a) (q+1),?_,
    ⟨rf,_,_,rfl⟩,?_,?_⟩
  · simpa [cost] using hn
  · simp [LeafProgram.foldEffect,read,update,state,unary]
  · rw [parser_state,parser_state,hreset]
    exact he

def program := LeafProgram.foldProgram ports callback

theorem fold_update (mask : List Bool) (scopes : List (List ℕ)) (a q : ℕ) :
    (scopes.map (Encoding.encodeList Encoding.encodeNat)).foldl (fun t bits => update mask bits t) (a,q) =
      (arity mask scopes a,q+scopes.length) := by
  induction scopes generalizing a q with
  | nil => simp [arity]
  | cons scope scopes ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [show update mask (Encoding.encodeList Encoding.encodeNat scope) (a,q) =
      (max (scope.filter (Scope.low mask)).length a,q+1) by simp [update]]
    rw [ih]
    simp [arity,Nat.add_comm,Nat.add_left_comm]

theorem program_runsIn (r : Fin 10 → Bool) (mask : List Bool) (scopes : List (List ℕ))
    (hv : ∀ scope ∈ scopes, ∀ v ∈ scope, v < mask.length) :
    ∃ rf, RunsIn program
      (4+RecordPrograms.budget (cost mask) (scopes.map (Encoding.encodeList Encoding.encodeNat)))
      ((RecordPrograms.state ports (state r mask [] [] [] 0 0) false true false
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) scopes) []).withPC (some program.entry))
      ((state rf mask [] [] [] (arity mask scopes 0) scopes.length).withPC none) := by
  obtain ⟨next,hn,hvalue,he⟩ := LeafProgram.foldProgram_run ports callback read (update mask)
    (cost mask) (invariant mask)
    (fun bits => ∃ scope, (∀ v ∈ scope, v < mask.length) ∧ Encoding.encodeList Encoding.encodeNat scope = bits)
    (callback_contract mask) (scopes.map (Encoding.encodeList Encoding.encodeNat)) []
    (state r mask [] [] [] 0 0)
    (by intro bits hb; obtain ⟨scope,hm,rfl⟩ := List.mem_map.mp hb; exact ⟨scope,hv scope hm,rfl⟩)
    ⟨r,0,0,rfl⟩ false true false
  obtain ⟨rf,a,q,rfl⟩ := hn
  have hread (rr : Fin 10 → Bool) (aa qq : ℕ) :
      read (state rr mask [] [] [] aa qq) = (aa,qq) := by
    simp [read,state,unary]
  have hvv : (a,q) = (arity mask scopes 0,scopes.length) := by
    rw [hread,hread,fold_update] at hvalue
    simpa only [Nat.zero_add] using hvalue
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hvv
  refine ⟨parserRegs rf false true false,?_⟩
  have hencode : ∀ xs : List (List ℕ), Encoding.encodeList id (xs.map (Encoding.encodeList Encoding.encodeNat)) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons scope scopes ih => simp [Encoding.encodeList,ih]
  simpa only [List.append_nil,parser_state,hencode,program] using he

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
