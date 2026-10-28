import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputEmit
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramPairs
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanProgram
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 6 9
abbrev unary (n : ℕ) := List.replicate n true
def data (r : Fin 6 → Bool) (h n : ℕ) (source out payload : List Bool)
    (factor : List Bool := []) : Data :=
  ⟨r, ![unary h,unary n,payload,factor,[],[],[],out,source]⟩
def recordPrefix (h n j : ℕ) : List Bool :=
  true :: Encoding.frame (Encoding.frame (Emit.plan h (n+j)))
def prefixes (h n : ℕ) (js : List ℕ) : List Bool := js.flatMap (recordPrefix h n)

abbrev copy : Cmd 6 9 := .call (StackRoutines.copyProgram 1 3 4 0 1)
def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 1 3 d.stacks⟩
abbrev transfer : Cmd 6 9 := .call (StackRoutines.transferProgram 2 3 0 1)
def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 2 3 d.stacks⟩
abbrev clear : Cmd 6 9 := .call (StackRoutines.clearProgram 3 0 1)
def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 3 []⟩

def registers : Fin 3 → Fin 6 := Fin.castAdd 3
def ports : Fin 6 → Fin 9 := ![0,3,4,5,6,7]
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 3 3
theorem ports_injective : Function.Injective ports := by decide
abbrev emit : Cmd 6 9 := .call
  (ProgramLinking.liftProgram (compiled Emit.command 0 5) registers ports)
abbrev callback : Cmd 6 9 := .seq copy (.seq transfer (.seq emit clear))
def callbackBound (h n j : ℕ) : ℕ := 200*(h+n+j+1)

theorem callback_eval (r : Fin 6 → Bool) (h n j : ℕ) (source out : List Bool) :
    ∃ t rf, t ≤ callbackBound h n j ∧
      Eval callback t (data r h n source out (unary j))
        (data rf h n source (recordPrefix h n j ++ out) []) ∧
      (∀ i : Fin 6, 3 ≤ i.val → rf i = r i) := by
  let a := data r h n source out (unary j)
  let b := copied a
  let c := transferred b
  have h1 : Eval copy (7*n+5) a b := by
    simpa [copy,b,copied,a,data] using TupleProgram.copy_eval (1 : Fin 9) 3 4 (0 : Fin 6) 1
      (by decide) (by decide) (by decide) (by decide) a (by rfl)
  have h2 : Eval transfer (3*j+3) b c := by
    simpa [c,transferred,b,copied,a,data,StackRoutines.copyStacks] using
      TupleProgram.transfer_eval (2 : Fin 9) 3 (0 : Fin 6) 1 (by decide) (by decide) b
  obtain ⟨re, h3base⟩ := Emit.command_eval (c.regs ∘ registers) h (n+j) out
  let small := Emit.data (c.regs ∘ registers) (unary h) (unary (n+j)) [] [] [] out
  let smallOut := Emit.data re (unary h) (unary (n+j)) [] [] [] (recordPrefix h n j ++ out)
  have hin : embedState registers ports c small = c := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [small,Emit.data,ports,c,transferred,b,copied,a,data,
          StackRoutines.transferStacks,StackRoutines.copyStacks,Nat.add_comm]
    · intros; rfl
  let d := embedState registers ports c smallOut
  have h3 : Eval emit (60*(h+(n+j))+174) c d := by
    have hh := eval_call_lifted (compiled Emit.command 0 5) registers ports c
      registers_injective ports_injective (compiled_halt_trace h3base 0 5)
    change Eval emit _ (embedState registers ports c small) d at hh
    rw [hin] at hh
    convert hh using 1
  have hd : d.stacks = (data d.regs h n source (recordPrefix h n j ++ out) [] (unary (n+j))).stacks := by
    funext i
    by_cases hi : ∃ k, ports k = i
    · obtain ⟨k,rfl⟩ := hi
      rw [show d.stacks (ports k) = smallOut.stacks k from
        embedState_stack registers ports c smallOut ports_injective k]
      fin_cases k <;> rfl
    · rw [show d.stacks i = c.stacks i from
        embedState_stack_frame registers ports c smallOut i hi]
      have hi0 : i ≠ 0 := fun hh => hi ⟨0,hh.symm⟩
      have hi3 : i ≠ 3 := fun hh => hi ⟨1,hh.symm⟩
      have hi4 : i ≠ 4 := fun hh => hi ⟨2,hh.symm⟩
      have hi5 : i ≠ 5 := fun hh => hi ⟨3,hh.symm⟩
      have hi6 : i ≠ 6 := fun hh => hi ⟨4,hh.symm⟩
      have hi7 : i ≠ 7 := fun hh => hi ⟨5,hh.symm⟩
      fin_cases i <;> simp_all [c,transferred,b,copied,a,data,
        StackRoutines.transferStacks,StackRoutines.copyStacks]
  have h4 : Eval clear (2*(n+j)+3) d (cleared d) := by
    have hh := TupleProgram.clear_eval (3 : Fin 9) (0 : Fin 6) 1 d
    simpa [hd,data,clear,cleared,StackRoutines.clearStacks] using hh
  have hend : cleared d = data (cleared d).regs h n source (recordPrefix h n j ++ out) [] := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i; simp only [hd]; fin_cases i <;> simp [data]
  have hf (i : Fin 6) (hi : 3 ≤ i.val) : (cleared d).regs i = r i := by
    have hi0 : i ≠ 0 := by intro hh; subst i; omega
    have hi1 : i ≠ 1 := by intro hh; subst i; omega
    have hr : ¬ ∃ k, registers k = i := by
      rintro ⟨k,hk⟩; subst i; fin_cases k <;> simp [registers] at hi
    have hh := embedState_register_frame registers ports c smallOut i hr
    simp only [cleared,readRegs,Function.update_of_ne hi0,Function.update_of_ne hi1]
    rw [show d.regs i = c.regs i from hh]
    simp [c,transferred,b,copied,a,data,readRegs,hi0,hi1]
  have hh := h1.seq (h2.seq (h3.seq h4))
  rw [hend] at hh
  exact ⟨_,(cleared d).regs,by dsimp [callbackBound]; omega,hh,hf⟩

def readerPorts : RecordPrograms.Ports 6 9 :=
  ⟨3,4,5,8,2,by decide,by decide,by decide,by decide⟩
abbrev command : Cmd 6 9 := RecordPrograms.iterate readerPorts callback
def budget (h n : ℕ) : List ℕ → ℕ
  | [] => 0
  | j::js => 6*j + callbackBound h n j + 7 + budget h n js

private theorem state_data (r : Fin 6 → Bool) (h n : ℕ)
    (source out payload : List Bool) (t pr f : Bool) (src pay : List Bool) :
    RecordPrograms.state readerPorts (data r h n source out payload) t pr f src pay =
      data (Function.update (Function.update (Function.update r 3 t) 4 pr) 5 f)
        h n src out pay := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> simp [readerPorts,data]

theorem loop_eval (js : List ℕ) (r : Fin 6 → Bool) (h n : ℕ) (out suffix : List Bool) :
    ∃ t rf, t ≤ 1+budget h n js ∧
      Eval (RecordPrograms.loop readerPorts callback) t
        (RecordMappedPrograms.afterTag readerPorts unary (data r h n [] out []) js suffix)
        (data rf h n suffix (prefixes h n js.reverse ++ out) []) ∧
      rf 3 = false ∧ rf 4 = true ∧ rf 5 = false := by
  induction js generalizing r out with
  | nil =>
      let rf := Function.update (Function.update (Function.update r 3 false) 4 true) 5 false
      refine ⟨1,rf,by simp [budget],?_,by simp [rf],by simp [rf],by simp [rf]⟩
      have hs : RecordMappedPrograms.afterTag readerPorts unary (data r h n [] out []) [] suffix =
          data rf h n suffix out [] := state_data r h n [] out [] false true false suffix []
      rw [hs]
      simpa [prefixes] using
        (Eval.while_false (test := readerPorts.tag) (body := RecordPrograms.body readerPorts callback)
          (a := data rf h n suffix out []) (by simp [data,rf,readerPorts]))
  | cons j js ih =>
      let tail := Encoding.encodeList unary js ++ suffix
      let ra := Function.update (Function.update (Function.update r 3 false) 4 true) 5 false
      obtain ⟨tc,rc,htc,hcb,hfr⟩ := callback_eval ra h n j tail out
      have hr3 : rc 3 = false := by simpa [ra] using hfr 3 (by decide)
      have hr4 : rc 4 = true := by simpa [ra] using hfr 4 (by decide)
      have hr5 : rc 5 = false := by simpa [ra] using hfr 5 (by decide)
      have hread := RecordPrograms.reader_eval readerPorts (data r h n [] out [])
        (unary j) tail [] true true false
      have hin : RecordMappedPrograms.afterTag readerPorts unary (data r h n [] out [])
          (j::js) suffix = RecordPrograms.state readerPorts (data r h n [] out []) true true false
          (Encoding.frame (unary j) ++ tail) [] := rfl
      rw [← hin] at hread
      simp only [List.append_nil,List.reverse_replicate] at hread
      rw [state_data] at hread
      have hs : RecordPrograms.state readerPorts (data rc h n [] (recordPrefix h n j ++ out) [])
          false true false tail [] = data rc h n tail (recordPrefix h n j ++ out) [] := by
        rw [state_data]
        congr 1
        funext i; fin_cases i <;> simp [hr3,hr4,hr5]
      have hpop := RecordMappedPrograms.pop_list_eval readerPorts unary
        (data rc h n [] (recordPrefix h n j ++ out) []) js suffix false true
      change Eval _ _ (RecordPrograms.state readerPorts _ false true false tail []) _ at hpop
      rw [hs] at hpop
      have hbranch := Eval.ite_false (yes := RecordPrograms.atom (.set readerPorts.tag false))
        (show (data rc h n tail (recordPrefix h n j ++ out) []).regs readerPorts.found = false from hr5) hpop
      obtain ⟨tr,rr,htr,hrest,hrf⟩ := ih rc (recordPrefix h n j ++ out)
      have hg : (RecordMappedPrograms.afterTag readerPorts unary (data r h n [] out [])
          (j::js) suffix).regs readerPorts.tag = true := by simp [RecordMappedPrograms.afterTag]
      have he := Eval.while_true hg (hread.seq (hcb.seq hbranch)) hrest
      refine ⟨6*j+4+(tc+2)+tr+1,rr,?_,?_,hrf⟩
      · simpa only [List.length_replicate] using (show
          (6*j+4+(tc+2))+tr+1 ≤ 1+budget h n (j::js) by simp only [budget]; omega)
      · simpa [RecordPrograms.loop,RecordPrograms.body,prefixes,List.reverse_cons,
          List.flatMap_append,List.append_assoc] using he

theorem command_eval (js : List ℕ) (r : Fin 6 → Bool) (h n : ℕ) (out suffix : List Bool) :
    ∃ t rf, t ≤ 3+budget h n js ∧
      Eval command t (data r h n (Encoding.encodeList unary js ++ suffix) out [])
        (data rf h n suffix (prefixes h n js.reverse ++ out) []) := by
  obtain ⟨t,rf,ht,he,_⟩ := loop_eval js r h n out suffix
  have hs := RecordPrograms.set_found_eval readerPorts (data r h n [] out [])
    (r 3) (r 4) (r 5) false (Encoding.encodeList unary js ++ suffix) []
  have hp := RecordMappedPrograms.pop_list_eval readerPorts unary
    (data r h n [] out []) js suffix (r 3) (r 4)
  have hh := hs.seq (hp.seq he)
  have hin : RecordPrograms.state readerPorts (data r h n [] out []) (r 3) (r 4) (r 5)
      (Encoding.encodeList unary js ++ suffix) [] =
      data r h n (Encoding.encodeList unary js ++ suffix) out [] := by
    rw [state_data]; simp only [Function.update_eq_self]
  rw [hin] at hh
  exact ⟨1+(1+t),rf,by omega,hh⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 16 32
abbrev unary (n : ℕ) := List.replicate n true
def scopeBits (scopes : List (List ℕ)) := Encoding.encodeList
  (Encoding.encodeList Encoding.encodeNat) scopes
def indices (scopes : List (List ℕ)) (v : ℕ) := IncidencePlanSpec.incidentIndices scopes v
theorem records_map (js : List ℕ) :
    ProgramEncoding.encodeRecords (js.map unary) = Encoding.encodeList unary js := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [ProgramEncoding.encodeRecords,Encoding.encodeList] at ih ⊢; exact ih
def data (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) : Data :=
  ⟨r, fun j => if j=20 then scopeBits scopes else if j=21 then unary n
    else if j=22 then unary v else if j=24 then unary z else if j=25 then out
    else if j=26 then mask else []⟩
def result (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) : Data :=
  ⟨r, fun j => if j=2 then (Encoding.encodeNat v).reverse
    else if j=5 then unary scopes.length
    else if j=7 then Encoding.encodeList unary (indices scopes v).reverse
    else if j=9 then unary (indices scopes v).length
    else (data r scopes n v z mask out).stacks j⟩

abbrev copy (src dst : Fin 32) : Cmd 16 32 :=
  .call (StackRoutines.copyProgram src dst 31 0 1)
def copied (src dst : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩
theorem copy_eval (src dst : Fin 32) (hsd : src ≠ dst) (hs : src ≠ 31)
    (hd : (31 : Fin 32) ≠ dst) (d : Data) (ht : d.stacks 31 = []) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  TupleProgram.copy_eval src dst 31 0 1 hsd hs hd (by decide) d ht

abbrev prepare : Cmd 16 32 := .seq (copy 20 6) (.seq (copy 22 2)
  (.seq (TupleProgram.pushConst 2 0 false) (TupleProgram.pushConst 7 0 false)))
def prepared (d : Data) : Data := TupleProgram.pushedState 7 0 false
  (TupleProgram.pushedState 2 0 false (copied 22 2 (copied 20 6 d)))

theorem prepare_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    Eval prepare (7*((scopeBits scopes).length+v)+14) (data r scopes n v z mask out)
      (prepared (data r scopes n v z mask out)) := by
  let a := data r scopes n v z mask out
  let b := copied 20 6 a
  let c := copied 22 2 b
  let d := TupleProgram.pushedState 2 0 false c
  have h1 := copy_eval 20 6 (by decide) (by decide) (by decide) a (by simp [a,data])
  have h2 := copy_eval 22 2 (by decide) (by decide) (by decide) b
    (by simp [b,copied,a,data,StackRoutines.copyStacks])
  have h3 := TupleProgram.pushConst_eval (2 : Fin 32) (0 : Fin 16) false c
  have h4 := TupleProgram.pushConst_eval (7 : Fin 32) (0 : Fin 16) false d
  have hh := h1.seq (h2.seq (h3.seq h4))
  convert hh using 1 <;>
    simp [prepared, a, b, c, d, copied, data, StackRoutines.copyStacks,
      Nat.mul_add, Nat.add_assoc]
  omega

def registers : Fin 10 → Fin 16 := Fin.castAdd 6
def ports : Fin 10 → Fin 32 := Fin.castAdd 22
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 10 6
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective 10 22
abbrev scan : Cmd 16 32 := .call (ProgramLinking.liftProgram
  (compiled SubexpIncidencePlanScan.command 6 7) registers ports)
abbrev command : Cmd 16 32 := .seq prepare scan
def bound (scopes : List (List ℕ)) (v : ℕ) :=
  7*((scopeBits scopes).length+v)+18+SubexpIncidencePlanScan.scanBudget v 0 scopes

theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    ∃ t rf, t ≤ bound scopes v ∧
      Eval command t (data r scopes n v z mask out) (result rf scopes n v z mask out) ∧
      (∀ i : Fin 16, 10 ≤ i.val → rf i = r i) := by
  let a := data r scopes n v z mask out
  let b := prepared a
  obtain ⟨t,rs,hs,_,_,_,ht⟩ := SubexpIncidencePlanScan.command_eval scopes
    (b.regs ∘ registers) v 0 0 [false] []
  let small := SubexpIncidencePlanScan.data (b.regs ∘ registers) v 0
    (scopeBits scopes) [false] [] 0
  let smallOut := SubexpIncidencePlanScan.data rs v scopes.length []
    (Encoding.encodeList unary (indices scopes v).reverse) [] (indices scopes v).length
  have hin : embedState registers ports b small = b := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [small,SubexpIncidencePlanScan.data,b,prepared,copied,a,data,
          TupleProgram.pushedState,StackRoutines.copyStacks,ports,Encoding.encodeNat,
          scopeBits]
    · intros; rfl
  have hs' : Eval SubexpIncidencePlanScan.command t small smallOut := by
    simpa [small,smallOut,indices,IncidencePlanSpec.incidentIndices,scopeBits,
      SubexpIncidencePlanScan.scopeBytes,SubexpIncidencePlanProgram.encode_indexPrefix,
      ← List.map_reverse,records_map] using hs
  let e := embedState registers ports b smallOut
  have he := eval_call_lifted (compiled SubexpIncidencePlanScan.command 6 7)
    registers ports b registers_injective ports_injective (compiled_halt_trace hs' 6 7)
  rw [hin] at he
  have hout : e = result e.regs scopes n v z mask out := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    change e.stacks i = (result e.regs scopes n v z mask out).stacks i
    by_cases hi : i.val < 10
    · let k : Fin 10 := ⟨i.val,hi⟩
      have hik : ports k = i := Fin.ext rfl
      rw [← hik,show e.stacks (ports k) = smallOut.stacks k from
        embedState_stack registers ports b smallOut ports_injective k]
      clear_value k
      fin_cases k <;> simp [smallOut,SubexpIncidencePlanScan.data,result,ports,data]
    · have hframe : ¬ ∃ k, ports k = i := by
        rintro ⟨k,hk⟩
        apply hi
        have hval := congrArg Fin.val hk
        simpa [ports] using hval ▸ k.isLt
      rw [show e.stacks i = b.stacks i from
        embedState_stack_frame registers ports b smallOut i hframe]
      have h2 : i ≠ 2 := by intro h; subst i; omega
      have h5 : i ≠ 5 := by intro h; subst i; omega
      have h6 : i ≠ 6 := by intro h; subst i; omega
      have h7 : i ≠ 7 := by intro h; subst i; omega
      have h9 : i ≠ 9 := by intro h; subst i; omega
      simp [b,prepared,copied,a,result,data,TupleProgram.pushedState,
        StackRoutines.copyStacks,h2,h5,h6,h7,h9]
  change Eval scan (t+1) b e at he
  rw [hout] at he
  refine ⟨_,e.regs,by dsimp [bound]; omega,(prepare_eval r scopes n v z mask out).seq he,?_⟩
  intro i hi
  have hr : ¬ ∃ k, registers k = i := by
    rintro ⟨k,hk⟩
    have hv := congrArg Fin.val hk
    have hlt := k.isLt
    change k.val = i.val at hv
    omega
  have hh := embedState_register_frame registers ports b smallOut i hr
  have hi0 : i ≠ 0 := by intro h; subst i; omega
  have hi1 : i ≠ 1 := by intro h; subst i; omega
  change e.regs i = b.regs i at hh
  rw [hh]
  simp [b,prepared,copied,a,data,TupleProgram.pushedState,readRegs,hi0,hi1]
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

namespace Clear
abbrev Data := Scan.Data
abbrev one (j : Fin 32) : Cmd 16 32 := .call (StackRoutines.clearProgram j 0 1)
def after (j : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks j []⟩
theorem one_eval (j : Fin 32) (d : Data) :
    Eval (one j) (2*(d.stacks j).length+3) d (after j d) := by
  simpa [one,after,StackRoutines.clearStacks] using
    TupleProgram.clear_eval j (0 : Fin 16) 1 d
def command : List (Fin 32) → Cmd 16 32
  | [] => .base .skip
  | j::js => .seq (one j) (command js)
theorem command_eval (js : List (Fin 32)) (d : Data) (B : ℕ)
    (hB : ∀ j ∈ js, (d.stacks j).length ≤ B) :
    ∃ t e, t ≤ js.length*(2*B+3)+1 ∧ Eval (command js) t d e ∧
      (∀ j, e.stacks j = if j ∈ js then [] else d.stacks j) ∧
      (∀ i : Fin 16, i ≠ 0 → i ≠ 1 → e.regs i = d.regs i) := by
  induction js generalizing d with
  | nil => exact ⟨0,d,by simp,Eval.base (.skip d),by simp,by simp⟩
  | cons j js ih =>
      have hb : ∀ k ∈ js, ((after j d).stacks k).length ≤ B := by
        intro k hk
        by_cases h : k=j
        · simp [after,h]
        · simpa [after,h] using hB k (by simp [hk])
      obtain ⟨t,e,ht,he,hs,hr⟩ := ih (after j d) hb
      refine ⟨2*(d.stacks j).length+3+t,e,?_,(one_eval j d).seq he,?_,?_⟩
      · have hh := hB j (by simp)
        simp only [List.length_cons]
        nlinarith
      · intro k
        rw [hs]
        by_cases hkj : k=j <;> by_cases hmem : k ∈ js <;>
          simp [after,hkj,hmem]
      · intro i hi0 hi1
        simpa [after,readRegs,hi0,hi1] using hr i hi0 hi1
end Clear
end SubexponentialSAT.SqrtLog.PackingIncidenceInput


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := Scan.Data
def registers : Fin 6 → Fin 16 := Fin.castAdd 10
def ports : Fin 9 → Fin 32 := ![22,21,12,13,14,15,16,25,7]
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 6 10
theorem ports_injective : Function.Injective ports := by decide
abbrev command (c : Cmd 6 9) : Cmd 16 32 :=
  .call (ProgramLinking.liftProgram (compiled c 8 7) registers ports)

def work (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out source payload : List Bool) : Data :=
  ⟨r, fun j => if j=2 then (Encoding.encodeNat v).reverse
    else if j=5 then Scan.unary scopes.length
    else if j=7 then source else if j=9 then Scan.unary (Scan.indices scopes v).length
    else if j=12 then payload else (Scan.data r scopes n v z mask out).stacks j⟩

theorem scan_eq_work (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    Scan.result r scopes n v z mask out = work r scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) [] := by
  apply congrArg (StructuredProgram.State.mk r)
  funext i; fin_cases i <;> simp [Scan.data]

theorem command_eval (c : Cmd 6 9) (r : Fin 16 → Bool) (scopes : List (List ℕ))
    (n v z : ℕ) (mask out source payload out' source' : List Bool)
    (t : ℕ) (rf : Fin 6 → Bool)
    (he : Eval c t (Rows.data (r ∘ registers) v n source out payload)
      (Rows.data rf v n source' out' [])) :
    ∃ rr, Eval (command c) (t+1)
      (work r scopes n v z mask out source payload)
      (work rr scopes n v z mask out' source' []) ∧
      (∀ i : Fin 16, 6 ≤ i.val → rr i = r i) := by
  let a := work r scopes n v z mask out source payload
  let small := Rows.data (r ∘ registers) v n source out payload
  let smallOut := Rows.data rf v n source' out' []
  have hin : embedState registers ports a small = a := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [a,small,Rows.data,work,Scan.data,ports]
    · intros; rfl
  let e := embedState registers ports a smallOut
  have hh := eval_call_lifted (compiled c 8 7) registers ports a
    registers_injective ports_injective (compiled_halt_trace he 8 7)
  rw [hin] at hh
  have hout : e = work e.regs scopes n v z mask out' source' [] := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    change e.stacks i = (work e.regs scopes n v z mask out' source' []).stacks i
    by_cases hi : ∃ k, ports k = i
    · obtain ⟨k,rfl⟩ := hi
      rw [show e.stacks (ports k) = smallOut.stacks k from
        embedState_stack registers ports a smallOut ports_injective k]
      fin_cases k <;> simp [smallOut,Rows.data,work,Scan.data,ports]
    · rw [show e.stacks i = a.stacks i from
        embedState_stack_frame registers ports a smallOut i hi]
      have h7 : i ≠ 7 := fun h => hi ⟨8,h.symm⟩
      have h12 : i ≠ 12 := fun h => hi ⟨2,h.symm⟩
      have h25 : i ≠ 25 := fun h => hi ⟨7,h.symm⟩
      simp [a,work,Scan.data,h7,h12,h25]
  change Eval (command c) (t+1) a e at hh
  rw [hout] at hh
  refine ⟨e.regs,hh,?_⟩
  intro i hi
  apply embedState_register_frame
  rintro ⟨k,hk⟩
  have hv := congrArg Fin.val hk
  have hlt := k.isLt
  change k.val = i.val at hv
  omega

abbrev clean : Cmd 16 32 := Clear.command [2,5,7,9]
def cleanBound (scopes : List (List ℕ)) (v : ℕ) (source : List Bool) :=
  8*(v+scopes.length+(Scan.indices scopes v).length+source.length+1)+13

theorem clean_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out source : List Bool) :
    ∃ t rf, t ≤ cleanBound scopes v source ∧
      Eval clean t (work r scopes n v z mask out source [])
        (Scan.data rf scopes n v z mask out) ∧
      (∀ i : Fin 16, 2 ≤ i.val → rf i = r i) := by
  let a := work r scopes n v z mask out source []
  let B := v+scopes.length+(Scan.indices scopes v).length+source.length+1
  have hB : ∀ j ∈ ([2,5,7,9] : List (Fin 32)), (a.stacks j).length ≤ B := by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl <;>
      simp [a,work,Scan.data,Encoding.encodeNat,B] <;> omega
  obtain ⟨t,e,ht,he,hs,hr⟩ := Clear.command_eval [2,5,7,9] a B hB
  have hout : e = Scan.data e.regs scopes n v z mask out := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    rw [hs]
    fin_cases i <;> simp [a,work,Scan.data]
  rw [hout] at he
  refine ⟨t,e.regs,?_,he,?_⟩
  · dsimp [cleanBound,B] at *; omega
  · intro i hi
    exact hr i (by intro h; subst i; omega) (by intro h; subst i; omega)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := Scan.Data

def rows := Lift.command Rows.command
abbrev neutral : Cmd 16 32 := .seq (Scan.copy 24 12)
  (.seq (Lift.command Rows.callback) (TupleProgram.pushConst 24 0 true))
abbrev peek : Cmd 16 32 := .seq (.base (.atom (.pop 7 10 11)))
  (.base (.atom (.push 7 10)))
abbrev branch : Cmd 16 32 := .ite 10 rows neutral
abbrev command : Cmd 16 32 := .seq Scan.command (.seq peek (.seq branch Lift.clean))

def next (scopes : List (List ℕ)) (v z : ℕ) :=
  if Scan.indices scopes v = [] then z+1 else z
def factors (scopes : List (List ℕ)) (v z : ℕ) :=
  if Scan.indices scopes v = [] then [z] else Scan.indices scopes v
def output (scopes : List (List ℕ)) (n v z : ℕ) (out : List Bool) :=
  Rows.prefixes v n (factors scopes v z) ++ out
def bound (scopes : List (List ℕ)) (n v z : ℕ) :=
  Scan.bound scopes v + Rows.budget v n (Scan.indices scopes v).reverse +
    Rows.callbackBound v n z + 7*z +
    Lift.cleanBound scopes v [false] + 30

theorem peek_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    let source := Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse
    let bit := decide (Scan.indices scopes v ≠ [])
    let rr := readRegs r 10 11 (some bit)
    Eval peek 2 (Lift.work r scopes n v z mask out source [])
      (Lift.work rr scopes n v z mask out source []) := by
  dsimp only
  have h := (Eval.base (StructuredProgram.Eval.atom (.pop (7 : Fin 32) 10 11)
    (Lift.work r scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) []))).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (7 : Fin 32) 10) _))
  convert h using 1
  cases hh : (Scan.indices scopes v).reverse with
  | nil =>
      have he : Scan.indices scopes v = [] := List.reverse_eq_nil_iff.mp hh
      apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
        simp [Lift.work,Scan.data,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,
          Encoding.encodeList,he,readRegs]
  | cons j js =>
      have he : Scan.indices scopes v ≠ [] := by intro h; simp [h] at hh
      apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
        simp [Lift.work,Scan.data,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,
          Encoding.encodeList,he,readRegs]

theorem neutral_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out source : List Bool) :
    ∃ t rf, t ≤ 7*z+Rows.callbackBound v n z+8 ∧
      Eval neutral t (Lift.work r scopes n v z mask out source [])
        (Lift.work rf scopes n v (z+1) mask (Rows.recordPrefix v n z ++ out) source []) ∧
      (∀ i : Fin 16, 6 ≤ i.val → rf i = r i) := by
  let a := Lift.work r scopes n v z mask out source []
  let b := Scan.copied 24 12 a
  have hc := Scan.copy_eval 24 12 (by decide) (by decide) (by decide) a
    (by simp [a,Lift.work,Scan.data])
  have hb : b = Lift.work b.regs scopes n v z mask out source (Rows.unary z) := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i; fin_cases i <;> simp [b,Scan.copied,StackRoutines.copyStacks,a,Lift.work,Scan.data]
  obtain ⟨t,rr,ht,he,_⟩ := Rows.callback_eval (b.regs ∘ Lift.registers) v n z source out
  obtain ⟨rf,hf,hr⟩ := Lift.command_eval Rows.callback b.regs scopes n v z mask out source
    (Rows.unary z) (Rows.recordPrefix v n z ++ out) source t rr he
  rw [← hb] at hf
  let c := Lift.work rf scopes n v z mask (Rows.recordPrefix v n z ++ out) source []
  have hi := TupleProgram.pushConst_eval (24 : Fin 32) (0 : Fin 16) true c
  let d := TupleProgram.pushedState 24 0 true c
  have hd : d = Lift.work d.regs scopes n v (z+1) mask (Rows.recordPrefix v n z ++ out) source [] := by
    apply congrArg (StructuredProgram.State.mk d.regs)
    funext i; fin_cases i <;>
      simp [d,c,Lift.work,Scan.data,List.replicate_succ]
  change Eval _ _ c d at hi
  rw [hd] at hi
  refine ⟨_,d.regs,?_,hc.seq (hf.seq hi),?_⟩
  · simpa [a,Lift.work,Scan.data] using (show 7*z+5+(t+1+2) ≤
      7*z+Rows.callbackBound v n z+8 by omega)
  · intro i h6
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h1 : i ≠ 1 := by intro h; subst i; omega
    have hh := hr i h6
    simpa [d,c,TupleProgram.pushedState,b,Scan.copied,a,Lift.work,readRegs,h0,h1] using hh

theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    ∃ t rf, t ≤ bound scopes n v z ∧
      Eval command t (Scan.data r scopes n v z mask out)
        (Scan.data rf scopes n v (next scopes v z) mask (output scopes n v z out)) ∧
      (∀ i : Fin 16, 12 ≤ i.val → rf i = r i) := by
  obtain ⟨ts,rs,hts,hs,hrs⟩ := Scan.command_eval r scopes n v z mask out
  rw [Lift.scan_eq_work] at hs
  let bit := decide (Scan.indices scopes v ≠ [])
  let rp := readRegs rs 10 11 (some bit)
  have hp := peek_eval rs scopes n v z mask out
  change Eval peek 2
    (Lift.work rs scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) [])
    (Lift.work rp scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) []) at hp
  by_cases hempty : Scan.indices scopes v = []
  · simp only [hempty,List.reverse_nil,Encoding.encodeList] at hs hp
    have hbit : rp 10 = false := by simp [rp,bit,hempty,readRegs]
    obtain ⟨tb,rb,htb,hb,hrb⟩ := neutral_eval rp scopes n v z mask out [false]
    have hbranch := Eval.ite_false (test := 10) (yes := rows) hbit hb
    obtain ⟨tc,rc,htc,hc,hrc⟩ := Lift.clean_eval rb scopes n v (z+1) mask
      (Rows.recordPrefix v n z ++ out) [false]
    have he := hs.seq (hp.seq (hbranch.seq hc))
    refine ⟨ts+(2+((tb+1)+tc)),rc,?_,?_,?_⟩
    · dsimp [bound]; omega
    · simpa [command,branch,next,output,factors,hempty,Encoding.encodeList,
        Rows.prefixes] using he
    · intro i hi
      have h0 : i ≠ 10 := by intro h; subst i; omega
      have h1 : i ≠ 11 := by intro h; subst i; omega
      rw [hrc i (by omega),hrb i (by omega)]
      simpa [rp,readRegs,h0,h1] using hrs i (by omega)
  · have hbit : rp 10 = true := by simp [rp,bit,hempty,readRegs]
    obtain ⟨tb,rb,htb,hb⟩ := Rows.command_eval (Scan.indices scopes v).reverse
      (rp ∘ Lift.registers) v n out []
    simp only [List.append_nil,List.reverse_reverse] at hb
    obtain ⟨rr,hrun,hrr⟩ := Lift.command_eval Rows.command rp scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) []
      (Rows.prefixes v n (Scan.indices scopes v) ++ out) [] tb rb hb
    have hbranch := Eval.ite_true (test := 10) (no := neutral) hbit hrun
    obtain ⟨tc,rc,htc,hc,hrc⟩ := Lift.clean_eval rr scopes n v z mask
      (Rows.prefixes v n (Scan.indices scopes v) ++ out) []
    have he := hs.seq (hp.seq (hbranch.seq hc))
    refine ⟨ts+(2+((tb+1+1)+tc)),rc,?_,?_,?_⟩
    · dsimp [bound,Lift.cleanBound] at *; omega
    · simpa [command,branch,rows,next,output,factors,hempty] using he
    · intro i hi
      have h0 : i ≠ 10 := by intro h; subst i; omega
      have h1 : i ≠ 11 := by intro h; subst i; omega
      rw [hrc i (by omega),hrr i (by omega)]
      simpa [rp,readRegs,h0,h1] using hrs i (by omega)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Step


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := Scan.Data

def ports : UnaryForPrograms.Ports 16 32 := ⟨26,14,15⟩
abbrev body : Cmd 16 32 := .seq (.ite 14 (.base .skip) Step.command)
  (TupleProgram.pushConst 22 0 true)
def command := UnaryForPrograms.forCmd ports body
def rowPlans (scopes : List (List ℕ)) (n v z : ℕ) : List (List ℕ) :=
  (Step.factors scopes v z).map fun e => [v,n+e]
def finalCounter (scopes : List (List ℕ)) : ℕ → ℕ → List Bool → ℕ
  | _,z,[] => z
  | v,z,high::rest => finalCounter scopes (v+1)
      (if high then z else Step.next scopes v z) rest
def plans (scopes : List (List ℕ)) (n : ℕ) : ℕ → ℕ → List Bool → List (List ℕ)
  | _,_,[] => []
  | v,z,high::rest => plans scopes n (v+1)
      (if high then z else Step.next scopes v z) rest ++
        if high then [] else rowPlans scopes n v z
def recordPrefix (ps : List (List ℕ)) : List Bool :=
  ps.flatMap fun p => true :: Encoding.frame (Encoding.frame (CollisionStreamProgram.planBytes p))
def budget (scopes : List (List ℕ)) (n : ℕ) : ℕ → ℕ → List Bool → ℕ
  | _,_,[] => 2
  | v,z,high::rest => (if high then 2 else Step.bound scopes n v z+1)+4+
      budget scopes n (v+1) (if high then z else Step.next scopes v z) rest

theorem row_prefix (scopes : List (List ℕ)) (n v z : ℕ) :
    recordPrefix (rowPlans scopes n v z) = Rows.prefixes v n (Step.factors scopes v z) := by
  simp only [recordPrefix,rowPlans,Rows.prefixes,List.flatMap_map]
  rfl

theorem pop_data (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    UnaryForPrograms.popped ports (Scan.data r scopes n v z mask out) =
      Scan.data (readRegs r 14 15 mask.head?) scopes n v z mask.tail out := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> simp [ports,Scan.data]

theorem body_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (high : Bool) (mask out : List Bool) (hr : r 14 = high) :
    ∃ t rf, t ≤ (if high then 2 else Step.bound scopes n v z+1)+2 ∧
      Eval body t (Scan.data r scopes n v z mask out)
        (Scan.data rf scopes n (v+1) (if high then z else Step.next scopes v z) mask
          (recordPrefix (if high then [] else rowPlans scopes n v z) ++ out)) := by
  cases high
  · obtain ⟨t,rr,ht,he,_⟩ := Step.command_eval r scopes n v z mask out
    have hb := Eval.ite_false (test := 14) (yes := .base .skip) hr he
    let a := Scan.data rr scopes n v (Step.next scopes v z) mask (Step.output scopes n v z out)
    have hi := TupleProgram.pushConst_eval (22 : Fin 32) (0 : Fin 16) true a
    let b := TupleProgram.pushedState 22 0 true a
    have hend : b = Scan.data b.regs scopes n (v+1) (Step.next scopes v z) mask
        (recordPrefix (rowPlans scopes n v z) ++ out) := by
      apply congrArg (StructuredProgram.State.mk b.regs)
      funext i; fin_cases i <;>
        simp [a,Scan.data,List.replicate_succ,Step.output,row_prefix]
    change Eval _ _ a b at hi
    rw [hend] at hi
    refine ⟨t+3,b.regs,by simpa using Nat.add_le_add_right ht 3,?_⟩
    simpa [body] using hb.seq hi
  · let a := Scan.data r scopes n v z mask out
    have hb := Eval.ite_true (test := 14) (no := Step.command) hr (Eval.base (.skip a))
    have hi := TupleProgram.pushConst_eval (22 : Fin 32) (0 : Fin 16) true a
    let b := TupleProgram.pushedState 22 0 true a
    have hend : b = Scan.data b.regs scopes n (v+1) z mask out := by
      apply congrArg (StructuredProgram.State.mk b.regs)
      funext i; fin_cases i <;> simp [a,Scan.data,List.replicate_succ]
    change Eval _ _ a b at hi
    rw [hend] at hi
    refine ⟨3,b.regs,by simp,?_⟩
    simpa [body,recordPrefix] using hb.seq hi

theorem visits (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∀ (r : Fin 16 → Bool) (v z : ℕ) (out : List Bool),
    ∃ costs t rf, t ≤ budget scopes n v z mask ∧
      UnaryForPrograms.Visits ports body costs t (Scan.data r scopes n v z mask out)
        (Scan.data rf scopes n (v+mask.length) (finalCounter scopes v z mask) []
          (recordPrefix (plans scopes n v z mask) ++ out)) := by
  induction mask with
  | nil =>
      intro r v z out
      refine ⟨[],2,readRegs r 14 15 none,by simp [budget],?_⟩
      have h := UnaryForPrograms.Visits.done (p := ports) (body := body)
        (Scan.data r scopes n v z [] out) rfl
      rw [pop_data] at h
      simpa [plans,recordPrefix,finalCounter] using h
  | cons high mask ih =>
      intro r v z out
      let rp := readRegs r 14 15 (some high)
      have hbit : rp 14 = high := by simp [rp,readRegs]
      obtain ⟨tb,rb,htb,hb⟩ := body_eval rp scopes n v z high mask out hbit
      obtain ⟨costs,t,rf,ht,he⟩ := ih rb (v+1) (if high then z else Step.next scopes v z)
        (recordPrefix (if high then [] else rowPlans scopes n v z) ++ out)
      have hbp : Eval body tb
          (UnaryForPrograms.popped ports (Scan.data r scopes n v z (high::mask) out))
          (Scan.data rb scopes n (v+1) (if high then z else Step.next scopes v z) mask
            (recordPrefix (if high then [] else rowPlans scopes n v z) ++ out)) := by
        rw [pop_data]; exact hb
      have hx := UnaryForPrograms.Visits.step (p := ports) (body := body)
        (by simp [Scan.data,ports]) hbp (by rw [pop_data]; rfl) he
      refine ⟨tb::costs,tb+t+2,rf,?_,?_⟩
      · simp only [budget]; omega
      · simpa [plans,recordPrefix,List.flatMap_append,List.append_assoc,finalCounter,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx

theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    ∃ t rf, t ≤ budget scopes n v z mask ∧
      Eval command t (Scan.data r scopes n v z mask out)
        (Scan.data rf scopes n (v+mask.length) (finalCounter scopes v z mask) []
          (recordPrefix (plans scopes n v z mask) ++ out)) := by
  obtain ⟨costs,t,rf,ht,h⟩ := visits scopes n mask r v z out
  exact ⟨t,rf,ht,h.eval⟩

theorem prefix_terminated (ps : List (List ℕ)) :
    recordPrefix ps ++ [false] = ProgramEncoding.encodeRecords
      (PackingIncidenceProgram.planAlphabet ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa [recordPrefix,PackingIncidenceProgram.planAlphabet,ProgramEncoding.encodeRecords,
        Encoding.encodeList,List.append_assoc] using congrArg
          (fun tail => (true :: Encoding.frame (Encoding.frame (CollisionStreamProgram.planBytes p))) ++ tail) ih

theorem produces (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∃ t rf, t ≤ budget scopes n 0 scopes.length mask ∧
      Eval command t (Scan.data r scopes n 0 scopes.length mask [false])
        (Scan.data rf scopes n mask.length (finalCounter scopes 0 scopes.length mask) []
          (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet
            (plans scopes n 0 scopes.length mask)))) := by
  obtain ⟨t,rf,ht,h⟩ := command_eval r scopes n 0 scopes.length mask [false]
  exact ⟨t,rf,ht,by simpa only [Nat.zero_add,prefix_terminated] using h⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev Data := Scan.Data
def registers : Fin 2 → Fin 16 := Fin.castAdd 14
def ports : Fin 2 → Fin 32 := ![0,24]
theorem registers_injective : Function.Injective registers := Fin.castAdd_injective 2 14
theorem ports_injective : Function.Injective ports := by decide
abbrev count : Cmd 16 32 := .call (ProgramLinking.liftProgram
  SubexpScopeCountSetup.counterProgram registers ports)
abbrev command : Cmd 16 32 := .seq (Scan.copy 20 0)
  (.seq count (TupleProgram.pushConst 25 0 false))
def records (scopes : List (List ℕ)) : List (List Bool) :=
  scopes.map (Encoding.encodeList Encoding.encodeNat)
def budget (scopes : List (List ℕ)) :=
  7*(Scan.scopeBits scopes).length+7+SubexpSunflowerProgram.CountRecords.loopSteps (records scopes)

theorem scope_eq (scopes : List (List ℕ)) :
    Scan.scopeBits scopes = Encoding.encodeList id (records scopes) := by
  induction scopes with
  | nil => rfl
  | cons s ss ih => simpa [Scan.scopeBits,records,Encoding.encodeList] using ih

theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ)
    (mask : List Bool) :
    ∃ rf, Eval command (budget scopes) (Scan.data r scopes n 0 0 mask [])
      (Scan.data rf scopes n 0 scopes.length mask [false]) := by
  let a := Scan.data r scopes n 0 0 mask []
  let b := Scan.copied 20 0 a
  have hc := Scan.copy_eval 20 0 (by decide) (by decide) (by decide) a
    (by simp [a,Scan.data])
  let small := SubexpScopeCountSetup.counterState (b.regs 0) (b.regs 1)
    (Encoding.encodeList id (records scopes)) []
  let smallOut := SubexpScopeCountSetup.counterState false false [] (Scan.unary scopes.length)
  have hin : embedState registers ports b small = b := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [small,SubexpScopeCountSetup.counterState,ParserProgram.pair,ports,b,
          Scan.copied,StackRoutines.copyStacks,a,Scan.data,scope_eq]
    · intros; rfl
  have hs := SubexpScopeCountSetup.counter_trace (records scopes) (b.regs 0) (b.regs 1)
  have hs' : Trace SubexpScopeCountSetup.counterProgram
      (SubexpSunflowerProgram.CountRecords.loopSteps (records scopes))
      (small.withPC (some SubexpScopeCountSetup.counterProgram.entry)) (smallOut.withPC none) := by
    simpa [small,smallOut,records] using hs
  let c := embedState registers ports b smallOut
  have hcount := eval_call_lifted SubexpScopeCountSetup.counterProgram registers ports b
    registers_injective ports_injective hs'
  rw [hin] at hcount
  have hout : c = Scan.data c.regs scopes n 0 scopes.length mask [] := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    change c.stacks i = (Scan.data c.regs scopes n 0 scopes.length mask []).stacks i
    by_cases hi : ∃ k, ports k = i
    · obtain ⟨k,rfl⟩ := hi
      rw [show c.stacks (ports k) = smallOut.stacks k from
        embedState_stack registers ports b smallOut ports_injective k]
      fin_cases k <;> simp [smallOut,SubexpScopeCountSetup.counterState,ParserProgram.pair,ports,Scan.data]
    · rw [show c.stacks i = b.stacks i from
        embedState_stack_frame registers ports b smallOut i hi]
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h24 : i ≠ 24 := fun h => hi ⟨1,h.symm⟩
      simp [b,Scan.copied,StackRoutines.copyStacks,a,Scan.data,h0,h24]
  change Eval count _ b c at hcount
  rw [hout] at hcount
  let d := Scan.data c.regs scopes n 0 scopes.length mask []
  have hp := TupleProgram.pushConst_eval (25 : Fin 32) (0 : Fin 16) false d
  let e := TupleProgram.pushedState 25 0 false d
  have he : e = Scan.data e.regs scopes n 0 scopes.length mask [false] := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i; fin_cases i <;> simp [d,Scan.data]
  change Eval _ _ d e at hp
  rw [he] at hp
  refine ⟨e.regs,?_⟩
  convert hc.seq (hcount.seq hp) using 1 ; simp [budget,a,Scan.data] ; ring

abbrev fullCommand : Cmd 16 32 := .seq command Loop.command
def fullProgram := compiled fullCommand 20 25
def fullBudget (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  budget scopes + Loop.budget scopes n 0 scopes.length mask + 1

theorem full_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ)
    (mask : List Bool) :
    ∃ t rf, t+1 ≤ fullBudget scopes n mask ∧
      Eval fullCommand t (Scan.data r scopes n 0 0 mask [])
        (Scan.data rf scopes n mask.length (Loop.finalCounter scopes 0 scopes.length mask) []
          (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet
            (Loop.plans scopes n 0 scopes.length mask)))) := by
  obtain ⟨rb,hb⟩ := command_eval r scopes n mask
  obtain ⟨t,rf,ht,he⟩ := Loop.produces rb scopes n mask
  exact ⟨_,rf,by dsimp [fullBudget]; omega,hb.seq he⟩

theorem primitive_run (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ)
    (mask : List Bool) :
    ∃ rf, Computation.RunsIn (primitive fullProgram).step
      (primitiveOverhead fullProgram * fullBudget scopes n mask)
      (primitiveCfg fullProgram ((Scan.data r scopes n 0 0 mask []).withPC (some fullProgram.entry)))
      (primitiveCfg fullProgram ((Scan.data rf scopes n mask.length
        (Loop.finalCounter scopes 0 scopes.length mask) []
        (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet
          (Loop.plans scopes n 0 scopes.length mask)))).withPC none)) := by
  obtain ⟨t,rf,ht,he⟩ := full_eval r scopes n mask
  exact ⟨rf,BitProgram.primitive_execution fullProgram
    ⟨t+1,ht,compiled_halt_trace he 20 25⟩⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
