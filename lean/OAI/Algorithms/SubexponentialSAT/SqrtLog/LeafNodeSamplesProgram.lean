import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! A fixed indexed traversal of the actual framed node table. The installed
worker is a real command; its measured, frame-preserving execution remains an
explicit producer obligation. Neither the index nor a jet is semantic advice. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

structure Store where
  frame : Fin 768 → List Bool
  source : List Bool := []
  payload : List Bool := []
  nodesRev : List Bool := []
  jetsRev : List Bool := []
  temporary : List Bool := []
  index : List Bool := []
  node : List Bool := []
  jet : List Bool := []
  shape : List Bool := []
  nodesOut : List Bool := []
  jetsOut : List Bool := []

def tapes (s : Store) (i : Fin 768) : List Bool :=
  if i = 301 then s.source else
  if i = 302 then s.payload else
  if i = 303 then s.nodesRev else
  if i = 304 then s.jetsRev else
  if i = 305 then s.temporary else
  if i = 307 then s.index else
  if i = 78 then s.node else
  if i = 102 then s.jet else
  if i = 104 then s.shape else
  if i = 256 then s.nodesOut else
  if i = 265 then s.jetsOut else
  s.frame i

def state (regs : Fin 40 → Bool) (s : Store) : Data := ⟨regs,tapes s⟩

/-- The enclosing branch and marked-clause controllers occupy this bank. -/
def RegFrame (before after : Fin 40 → Bool) : Prop :=
  ∀ i, 16 ≤ i.val → i.val < 24 → after i = before i

theorem RegFrame.refl (regs : Fin 40 → Bool) : RegFrame regs regs := by
  intro i hi hj; rfl

theorem RegFrame.trans {a b c : Fin 40 → Bool}
    (hab : RegFrame a b) (hbc : RegFrame b c) : RegFrame a c := by
  intro i hi hj
  exact (hbc i hi hj).trans (hab i hi hj)

theorem readRegs_frame (regs : Fin 40 → Bool) : RegFrame regs (readRegs regs 0 1 none) := by
  intro i hi hj
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
  simp [readRegs,h0,h1]

theorem update_zero_frame (regs : Fin 40 → Bool) (b : Bool) :
    RegFrame regs (Function.update regs 0 b) := by
  intro i hi hj
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  simp [h0]

@[simp] theorem tapes_source (s : Store) : tapes s 301 = s.source := by simp [tapes]
@[simp] theorem update_source (s : Store) (bits : List Bool) :
    Function.update (tapes s) 301 bits = tapes {s with source := bits} := by
  funext i
  by_cases hi : i = 301
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_payload (s : Store) : tapes s 302 = s.payload := by simp [tapes]
@[simp] theorem update_payload (s : Store) (bits : List Bool) :
    Function.update (tapes s) 302 bits = tapes {s with payload := bits} := by
  funext i
  by_cases hi : i = 302
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_nodesRev (s : Store) : tapes s 303 = s.nodesRev := by simp [tapes]
@[simp] theorem update_nodesRev (s : Store) (bits : List Bool) :
    Function.update (tapes s) 303 bits = tapes {s with nodesRev := bits} := by
  funext i
  by_cases hi : i = 303
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_jetsRev (s : Store) : tapes s 304 = s.jetsRev := by simp [tapes]
@[simp] theorem update_jetsRev (s : Store) (bits : List Bool) :
    Function.update (tapes s) 304 bits = tapes {s with jetsRev := bits} := by
  funext i
  by_cases hi : i = 304
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_temporary (s : Store) : tapes s 305 = s.temporary := by simp [tapes]
@[simp] theorem update_temporary (s : Store) (bits : List Bool) :
    Function.update (tapes s) 305 bits = tapes {s with temporary := bits} := by
  funext i
  by_cases hi : i = 305
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_index (s : Store) : tapes s 307 = s.index := by simp [tapes]
@[simp] theorem update_index (s : Store) (bits : List Bool) :
    Function.update (tapes s) 307 bits = tapes {s with index := bits} := by
  funext i
  by_cases hi : i = 307
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_node (s : Store) : tapes s 78 = s.node := by simp [tapes]
@[simp] theorem update_node (s : Store) (bits : List Bool) :
    Function.update (tapes s) 78 bits = tapes {s with node := bits} := by
  funext i
  by_cases hi : i = 78
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_jet (s : Store) : tapes s 102 = s.jet := by simp [tapes]
@[simp] theorem update_jet (s : Store) (bits : List Bool) :
    Function.update (tapes s) 102 bits = tapes {s with jet := bits} := by
  funext i
  by_cases hi : i = 102
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_shape (s : Store) : tapes s 104 = s.shape := by simp [tapes]
@[simp] theorem update_shape (s : Store) (bits : List Bool) :
    Function.update (tapes s) 104 bits = tapes {s with shape := bits} := by
  funext i
  by_cases hi : i = 104
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_nodesOut (s : Store) : tapes s 256 = s.nodesOut := by simp [tapes]
@[simp] theorem update_nodesOut (s : Store) (bits : List Bool) :
    Function.update (tapes s) 256 bits = tapes {s with nodesOut := bits} := by
  funext i
  by_cases hi : i = 256
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_jetsOut (s : Store) : tapes s 265 = s.jetsOut := by simp [tapes]
@[simp] theorem update_jetsOut (s : Store) (bits : List Bool) :
    Function.update (tapes s) 265 bits = tapes {s with jetsOut := bits} := by
  funext i
  by_cases hi : i = 265
  · subst i; simp [tapes]
  · simp [tapes,hi]

def copy (src dst : Fin 768) : Code := .call (copyProgram src dst 305 (0 : Fin 40) 1)
def transfer (src dst : Fin 768) : Code := .call (transferProgram src dst (0 : Fin 40) 1)
def clear (src : Fin 768) : Code := .call (clearProgram src (0 : Fin 40) 1)

theorem copy_store (regs : Fin 40 → Bool) (a b : Store) (src dst : Fin 768)
    (hsd : src ≠ dst) (hst : src ≠ 305) (htd : (305 : Fin 768) ≠ dst)
    (htmp : a.temporary = []) (hout : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.copy_run src dst 305 0 1 hsd hst htd
    (by decide) regs (tapes a) (by simpa using htmp)
  apply Eval.call
  simpa only [state,ListRegisterProgram.Run,StructuredProgram.State.withPC,hout] using he

theorem transfer_store (regs : Fin 40 → Bool) (a b : Store) (src dst : Fin 768)
    (hsd : src ≠ dst) (hout : transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.transfer_run src dst (0 : Fin 40) 1 hsd (by decide) regs (tapes a)
  apply Eval.call
  simpa only [state,ListRegisterProgram.Run,StructuredProgram.State.withPC,hout] using he

theorem clear_store (regs : Fin 40 → Bool) (a b : Store) (src : Fin 768)
    (hout : Function.update (tapes a) src [] = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.clear_run src (0 : Fin 40) 1 regs (tapes a)
  apply Eval.call
  simpa only [state,ListRegisterProgram.Run,StructuredProgram.State.withPC,clearStacks,hout] using he

def ports : RecordPrograms.Ports 40 768 where
  tag := 37
  present := 38
  found := 39
  source := 301
  payload := 302
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def parserRegs (regs : Fin 40 → Bool) (v pr f : Bool) : Fin 40 → Bool :=
  Function.update (Function.update (Function.update regs 37 v) 38 pr) 39 f

theorem parserRegs_frame (regs : Fin 40 → Bool) (v pr f : Bool) :
    RegFrame regs (parserRegs regs v pr f) := by
  intro i hi hj
  have h37 : i ≠ 37 := by intro h; subst i; exact (by decide : ¬ ((37 : Fin 40).val < 24)) hj
  have h38 : i ≠ 38 := by intro h; subst i; exact (by decide : ¬ ((38 : Fin 40).val < 24)) hj
  have h39 : i ≠ 39 := by intro h; subst i; exact (by decide : ¬ ((39 : Fin 40).val < 24)) hj
  simp [parserRegs,h37,h38,h39]

theorem parserRegs_self (regs : Fin 40 → Bool) :
    parserRegs regs (regs 37) (regs 38) (regs 39) = regs := by
  funext i
  by_cases h13 : i = 37 <;> by_cases h14 : i = 38 <;> by_cases h15 : i = 39 <;>
    simp [parserRegs,h13,h14,h15]

theorem record_state (regs : Fin 40 → Bool) (s : Store)
    (v pr f : Bool) (src out : List Bool) :
    RecordPrograms.state ports (state regs s) v pr f src out =
      state (parserRegs regs v pr f) {s with source := src,payload := out} := by
  simp only [RecordPrograms.state,ports,state,parserRegs,update_source,update_payload]

def reader : Code := RecordPrograms.reader ports
def pop : Code := RecordPrograms.atom (.pop 301 37 38)

theorem reader_store (regs : Fin 40 → Bool) (s : Store) (bits tail : List Bool)
    (hs : s.source = Encoding.frame bits ++ tail) (hp : s.payload = []) :
    Eval reader (6*bits.length+4) (state regs s)
      (state (parserRegs regs false true (regs 39))
        {s with source := tail,payload := bits.reverse}) := by
  have he := RecordPrograms.reader_eval ports (state regs s) bits tail []
    (regs 37) (regs 38) (regs 39)
  rw [record_state,record_state,parserRegs_self] at he
  have hin : {s with source := Encoding.frame bits ++ tail,payload := []} = s := by
    rw [← hs,← hp]
  simpa only [reader,hin,List.append_nil] using he

theorem pop_store (regs : Fin 40 → Bool) (s : Store) (b : Bool) (tail : List Bool)
    (hs : s.source = b :: tail) :
    Eval pop 1 (state regs s)
      (state (parserRegs regs b true (regs 39)) {s with source := tail}) := by
  have he := RecordPrograms.pop_eval ports (state regs s) (regs 37) (regs 38) (regs 39)
    b tail s.payload
  rw [record_state,record_state,parserRegs_self] at he
  simpa [pop,ports,← hs] using he

def increment : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 307 0)))
theorem increment_store (regs : Fin 40 → Bool) (s : Store) :
    Eval increment 2 (state regs s)
      (state (Function.update regs 0 true) {s with index := true :: s.index}) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 40) true) (state regs s))).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (307 : Fin 768) 0) _))
  simpa [increment,state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h

structure Sample where
  node : List Bool
  jet : List Bool
  cost : ℕ

/-- This is an execution contract for the installed command, not a jet oracle.
It is quantified over arbitrary collector contents, which the worker frames. -/
def WorkerContract (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (samples : ℕ → Sample) (shape : List Bool) (Q : ℕ) : Prop :=
  ∀ i < Q, ∀ (regs : Fin 40 → Bool) (s : Store), Valid s.frame →
    s.index = List.replicate i true → s.node = (samples i).node →
    s.jet = [] → s.shape = [] →
    ∃ time ≤ (samples i).cost, ∃ rr,
      RegFrame regs rr ∧
      Eval worker time (state regs s)
        (state rr {s with node := [],jet := (samples i).jet,shape := shape})

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

/-- One real worker invocation, with physical node/index inputs. -/
def callback (worker : Code) : Code :=
  .seq (copy 302 303) (.seq (transfer 302 78) (.seq worker
    (.seq (transfer 102 304) (.seq (clear 104) increment))))

def advance (s : Store) (sample : Sample) : Store :=
  {s with index := true :: s.index, nodesRev := sample.node.reverse ++ s.nodesRev, jetsRev := sample.jet.reverse ++ s.jetsRev}

def callbackBudget (sample : Sample) (shape : List Bool) : ℕ :=
  sample.cost+10*sample.node.length+3*sample.jet.length+2*shape.length+16

theorem callback_eval (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (samples : ℕ → Sample) (shape : List Bool) (Q i : ℕ)
    (contract : WorkerContract worker Valid samples shape Q) (hi : i < Q)
    (regs : Fin 40 → Bool) (s : Store) (hv : Valid s.frame)
    (hx : s.index = List.replicate i true)
    (hp : s.payload = (samples i).node.reverse)
    (hn : s.node = []) (hj : s.jet = []) (hs : s.shape = [])
    (ht : s.temporary = []) :
    ∃ time ≤ callbackBudget (samples i) shape, ∃ rr,
      RegFrame regs rr ∧
      Eval (callback worker) time (state regs s)
        (state rr {advance s (samples i) with payload := []}) := by
  let a := {s with nodesRev := (samples i).node.reverse ++ s.nodesRev}
  let b := {a with payload := [],node := (samples i).node}
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  have h1 := copy_store regs s a 302 303 (by decide) (by decide) (by decide) ht
    (by simp [copyStacks,hp,a])
  have h2 := transfer_store r1 a b 302 78 (by decide)
    (by simp [transferStacks,a,b,hp,hn])
  obtain ⟨time,hbound,r3,hframe,h3⟩ := contract i hi r2 b hv
    (by simpa [b,a] using hx) rfl (by simpa [b,a] using hj) (by simpa [b,a] using hs)
  let c := {b with node := [],jet := (samples i).jet,shape := shape}
  let d := {c with jet := [],jetsRev := (samples i).jet.reverse ++ s.jetsRev}
  let e := {d with shape := []}
  let r4 := readRegs r3 0 1 none
  let r5 := readRegs r4 0 1 none
  have h4 := transfer_store r3 c d 102 304 (by decide)
    (by simp [transferStacks,c,d,b,a])
  have h5 := clear_store r4 d e 104 (by simp [e])
  have h6 := increment_store r5 e
  refine ⟨7*(tapes s 302).length+5+(3*(tapes a 302).length+3+
      (time+(3*(tapes c 102).length+3+(2*(tapes d 104).length+3+2)))),
      ?_,Function.update r5 0 true,?_,?_⟩
  · simp only [callbackBudget,tapes_payload,tapes_jet,tapes_shape,hp,List.length_reverse]
    dsimp [a,b,c,d]
    simp only [hp,List.length_reverse]
    omega
  · exact (readRegs_frame regs).trans ((readRegs_frame r1).trans
      (hframe.trans ((readRegs_frame r3).trans
        ((readRegs_frame r4).trans (update_zero_frame r5 true)))))
  · have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
    simpa [callback,advance,a,b,c,d,e,hn,hj,hs] using he

@[simp] theorem advance_frame (s : Store) (sample : Sample) :
    (advance s sample).frame = s.frame := rfl
@[simp] theorem advance_node (s : Store) (sample : Sample) :
    (advance s sample).node = s.node := rfl
@[simp] theorem advance_jet (s : Store) (sample : Sample) :
    (advance s sample).jet = s.jet := rfl
@[simp] theorem advance_shape (s : Store) (sample : Sample) :
    (advance s sample).shape = s.shape := rfl
@[simp] theorem advance_temporary (s : Store) (sample : Sample) :
    (advance s sample).temporary = s.temporary := rfl

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def records (samples : ℕ → Sample) (start : ℕ) : ℕ → List (List Bool)
  | 0 => []
  | count+1 => (samples start).node :: records samples (start+1) count

def jetRecords (samples : ℕ → Sample) (start : ℕ) : ℕ → List (List Bool)
  | 0 => []
  | count+1 => (samples start).jet :: jetRecords samples (start+1) count

def ready (regs : Fin 40 → Bool) (s : Store) (samples : ℕ → Sample) (start : ℕ) : ℕ → Data
  | 0 => state (parserRegs regs false true (regs 39)) {s with source := [],payload := []}
  | count+1 => state (parserRegs regs true true (regs 39))
      {s with source := Encoding.frame (samples start).node ++
        Encoding.encodeList id (records samples (start+1) count),payload := []}

def done (s : Store) (samples : ℕ → Sample) (start : ℕ) : ℕ → Store
  | 0 => {s with source := [],payload := []}
  | count+1 => done (advance s (samples start)) samples (start+1) count

def loop (worker : Code) : Code := .while 37 (.seq reader (.seq (callback worker) pop))

def loopBudget (samples : ℕ → Sample) (shape : List Bool) (start : ℕ) : ℕ → ℕ
  | 0 => 1
  | count+1 => 6*(samples start).node.length + callbackBudget (samples start) shape +
      6 + loopBudget samples shape (start+1) count

theorem pop_ready (regs : Fin 40 → Bool) (s : Store) (samples : ℕ → Sample)
    (start count : ℕ) :
    Eval pop 1
      (state regs {s with source := Encoding.encodeList id (records samples start count),payload := []})
      (ready regs s samples start count) := by
  cases count with
  | zero =>
    simpa [ready,records,Encoding.encodeList] using
      pop_store regs {s with source := [false],payload := []} false [] rfl
  | succ count =>
    simpa [ready,records,Encoding.encodeList] using
      pop_store regs {s with source := true :: (Encoding.frame (samples start).node ++
        Encoding.encodeList id (records samples (start+1) count)),payload := []}
        true (Encoding.frame (samples start).node ++ Encoding.encodeList id (records samples (start+1) count)) rfl

theorem loop_eval (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (samples : ℕ → Sample) (shape : List Bool) (Q : ℕ)
    (contract : WorkerContract worker Valid samples shape Q)
    (start count : ℕ) (hrange : start+count ≤ Q) (regs : Fin 40 → Bool)
    (s : Store) (hv : Valid s.frame) (hx : s.index = List.replicate start true)
    (hn : s.node = []) (hj : s.jet = []) (hs : s.shape = []) (ht : s.temporary = []) :
    ∃ time ≤ loopBudget samples shape start count, ∃ rr,
      RegFrame regs rr ∧
      Eval (loop worker) time (ready regs s samples start count)
        (state rr (done s samples start count)) := by
  induction count generalizing start regs s with
  | zero =>
    refine ⟨1,le_rfl,parserRegs regs false true (regs 39),parserRegs_frame _ _ _ _,?_⟩
    apply Eval.while_false
    simp [ready,state,parserRegs]
  | succ count ih =>
    let tail := Encoding.encodeList id (records samples (start+1) count)
    let a := {s with source := Encoding.frame (samples start).node ++ tail,payload := []}
    let b := {s with source := tail,payload := (samples start).node.reverse}
    let r0 := parserRegs regs true true (regs 39)
    let r1 := parserRegs r0 false true (r0 39)
    have hread : Eval reader (6*(samples start).node.length+4)
        (ready regs s samples start (count+1)) (state r1 b) := by
      simpa [ready,a,b,tail,r0,r1] using reader_store r0 a (samples start).node tail rfl rfl
    obtain ⟨c,hc,r2,hcf,hcall⟩ := callback_eval worker Valid samples shape Q start contract
      (by omega) r1 b hv (by simpa [b] using hx) rfl
      (by simpa [b] using hn) (by simpa [b] using hj)
      (by simpa [b] using hs) (by simpa [b] using ht)
    have hcall' : Eval (callback worker) c (state r1 b)
        (state r2 {advance s (samples start) with source := tail,payload := []}) := by
      simpa [b,advance] using hcall
    have hpop := pop_ready r2 (advance s (samples start)) samples (start+1) count
    have hx' : (advance s (samples start)).index = List.replicate (start+1) true := by
      simp [advance,hx,List.replicate_succ]
    obtain ⟨u,hu,r3,hrf,hrest⟩ := ih (start+1) (by omega) r2 (advance s (samples start)) hv
      hx' (by simpa using hn) (by simpa using hj) (by simpa using hs) (by simpa using ht)
    refine ⟨(6*(samples start).node.length+4+(c+1))+u+1,?_,r3,?_,?_⟩
    · simp only [loopBudget]
      omega
    · exact (parserRegs_frame regs true true (regs 39)).trans
        ((parserRegs_frame r0 false true (r0 39)).trans (hcf.trans hrf))
    · have hguard : (ready regs s samples start (count+1)).regs 37 = true := by
        simp [ready,state,parserRegs]
      have hbody := hread.seq (hcall'.seq hpop)
      simpa only [loop,done] using Eval.while_true hguard hbody hrest

theorem done_eq (s : Store) (samples : ℕ → Sample) (start count : ℕ) :
    done s samples start count =
      {s with source := [], payload := [], index := List.replicate count true ++ s.index, nodesRev := (records samples start count).flatten.reverse ++ s.nodesRev, jetsRev := (jetRecords samples start count).flatten.reverse ++ s.jetsRev} := by
  induction count generalizing start s with
  | zero => simp [done,records,jetRecords]
  | succ count ih =>
    rw [done,ih]
    simp [advance,records,jetRecords,List.reverse_append,List.append_assoc,
      List.replicate_succ]
    calc
      List.replicate count true ++ true :: s.index =
          (List.replicate count true ++ [true]) ++ s.index := by simp [List.append_assoc]
      _ = List.replicate (count+1) true ++ s.index := by rw [List.replicate_succ']
      _ = true :: (List.replicate count true ++ s.index) := by simp only [List.replicate_succ,List.cons_append]

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def initial (frame : Fin 768 → List Bool) (oldNodes : List Bool) : Store :=
  {frame := frame, nodesOut := oldNodes}

def finished (frame : Fin 768 → List Bool) (samples : ℕ → Sample) (Q : ℕ) : Store :=
  {frame := frame, nodesOut := (records samples 0 Q).flatten,
    jetsOut := (jetRecords samples 0 Q).flatten}

/-- The original scalar stream is retained throughout all callbacks. The final
clear and transfer physically restore that stream beside the ordered jets. -/
def collect (worker : Code) : Code :=
  .seq (copy 300 301) (.seq pop (.seq (loop worker)
    (.seq (clear 256) (.seq (transfer 303 256)
      (.seq (transfer 304 265) (clear 307))))))

def collectBudget (samples : ℕ → Sample) (shape oldNodes : List Bool) (Q : ℕ) : ℕ :=
  7*(Encoding.encodeList id (records samples 0 Q)).length +
    loopBudget samples shape 0 Q + 2*oldNodes.length +
    3*(records samples 0 Q).flatten.length +
    3*(jetRecords samples 0 Q).flatten.length + 2*Q + 18

theorem collect_eval (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (samples : ℕ → Sample) (shape : List Bool) (Q : ℕ)
    (contract : WorkerContract worker Valid samples shape Q)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records samples 0 Q)) :
    ∃ time ≤ collectBudget samples shape oldNodes Q, ∃ rr,
      RegFrame regs rr ∧
      Eval (collect worker) time (state regs (initial frame oldNodes))
        (state rr (finished frame samples Q)) := by
  let s := initial frame oldNodes
  let a := {s with source := Encoding.encodeList id (records samples 0 Q)}
  let r1 := readRegs regs 0 1 none
  have h300 : tapes s 300 = Encoding.encodeList id (records samples 0 Q) := by
    simpa [tapes,s,initial] using hsource
  have hc := copy_store regs s a 300 301 (by decide) (by decide) (by decide) rfl
    (by simp only [copyStacks,h300,tapes_source,update_source]; simp [a,s,initial])
  have hp := pop_ready r1 s samples 0 Q
  obtain ⟨time,htime,r2,hframe,hl⟩ := loop_eval worker Valid samples shape Q contract
    0 Q (by omega) r1 s hv rfl rfl rfl rfl rfl
  let b := done s samples 0 Q
  have hb : b = {frame := frame, nodesRev := (records samples 0 Q).flatten.reverse, jetsRev := (jetRecords samples 0 Q).flatten.reverse, index := List.replicate Q true, nodesOut := oldNodes : Store} := by
    simp [b,done_eq,s,initial]
  let c := {b with nodesOut := []}
  let d := {c with nodesRev := [],nodesOut := (records samples 0 Q).flatten}
  let e := {d with jetsRev := [],jetsOut := (jetRecords samples 0 Q).flatten}
  let f := {e with index := []}
  let r3 := readRegs r2 0 1 none
  let r4 := readRegs r3 0 1 none
  let r5 := readRegs r4 0 1 none
  let r6 := readRegs r5 0 1 none
  have hclear := clear_store r2 b c 256 (by simp [c])
  have hnodes := transfer_store r3 c d 303 256 (by decide)
    (by simp [transferStacks,c,d,hb])
  have hjets := transfer_store r4 d e 304 265 (by decide)
    (by simp [transferStacks,c,d,e,hb])
  have hindex := clear_store r5 e f 307 (by simp [f])
  refine ⟨(7*(tapes s 300).length+5)+(1+(time+
    ((2*(tapes b 256).length+3)+((3*(tapes c 303).length+3)+
      ((3*(tapes d 304).length+3)+(2*(tapes e 307).length+3)))))),?_,r6,?_,?_⟩
  · simp only [collectBudget,h300,tapes_nodesOut,tapes_nodesRev,tapes_jetsRev,tapes_index]
    simp only [c,d,e,hb,List.length_reverse,List.length_replicate]
    omega
  · exact (readRegs_frame regs).trans (hframe.trans ((readRegs_frame r2).trans
      ((readRegs_frame r3).trans ((readRegs_frame r4).trans (readRegs_frame r5)))))
  · have he := hc.seq (hp.seq (hl.seq (hclear.seq (hnodes.seq (hjets.seq hindex)))))
    simpa only [collect,a,f,e,d,c,hb,s,initial,finished] using he

/-- One fixed finite instruction table, independent of Q and all node values. -/
def collectProgram (worker : Code) := compiled (collect worker) 300 265

theorem collect_trace (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (samples : ℕ → Sample) (shape : List Bool) (Q : ℕ)
    (contract : WorkerContract worker Valid samples shape Q)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records samples 0 Q)) :
    ∃ time ≤ collectBudget samples shape oldNodes Q + 1, ∃ rr,
      RegFrame regs rr ∧
      Trace (collectProgram worker) time
        ((state regs (initial frame oldNodes)).withPC (some (collectProgram worker).entry))
        ((state rr (finished frame samples Q)).withPC none) := by
  obtain ⟨time,htime,rr,hf,he⟩ := collect_eval worker Valid samples shape Q contract
    frame oldNodes regs hv hsource
  exact ⟨time+1,Nat.add_le_add_right htime 1,rr,hf,compiled_halt_trace he 300 265⟩

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

theorem records_eq_range (samples : ℕ → Sample) (start count : ℕ) :
    records samples start count =
      (List.range' start count).map (fun i => (samples i).node) := by
  induction count generalizing start with
  | zero => simp [records]
  | succ count ih => simp only [records,List.range'_succ,List.map_cons,ih]

theorem jetRecords_eq_range (samples : ℕ → Sample) (start count : ℕ) :
    jetRecords samples start count =
      (List.range' start count).map (fun i => (samples i).jet) := by
  induction count generalizing start with
  | zero => simp [jetRecords]
  | succ count ih => simp only [jetRecords,List.range'_succ,List.map_cons,ih]

theorem records_eq_finRange (samples : ℕ → Sample) (Q : ℕ) :
    records samples 0 Q = (List.finRange Q).map (fun i => (samples i.val).node) := by
  rw [records_eq_range,← List.range_eq_range',← List.map_coe_finRange Q,List.map_map]
  rfl

theorem jetRecords_eq_finRange (samples : ℕ → Sample) (Q : ℕ) :
    jetRecords samples 0 Q = (List.finRange Q).map (fun i => (samples i.val).jet) := by
  rw [jetRecords_eq_range,← List.range_eq_range',← List.map_coe_finRange Q,List.map_map]
  rfl

/-- All Q worker executions and every parser/collector operation are charged. -/
theorem loopBudget_eq_sum (samples : ℕ → Sample) (shape : List Bool) (start count : ℕ) :
    loopBudget samples shape start count =
      ((List.range' start count).map (fun i => (samples i).cost +
        16*(samples i).node.length + 3*(samples i).jet.length + 2*shape.length + 22)).sum + 1 := by
  induction count generalizing start with
  | zero => simp [loopBudget]
  | succ count ih =>
    simp only [loopBudget,callbackBudget,List.range'_succ,List.map_cons,List.sum_cons,ih]
    omega

theorem encoded_records_length (samples : ℕ → Sample) (start count : ℕ) :
    (SubexponentialSAT.Encoding.encodeList id (records samples start count)).length =
      2*(records samples start count).flatten.length + 2*count + 1 := by
  induction count generalizing start with
  | zero => simp [records,SubexponentialSAT.Encoding.encodeList]
  | succ count ih =>
    simp only [records,SubexponentialSAT.Encoding.encodeList,List.length_cons,List.length_append,
      SubexponentialSAT.Encoding.length_frame,List.flatten_cons,ih,id_eq]
    omega

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

end OAI.Algorithms
