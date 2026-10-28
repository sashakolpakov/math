import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarCacheCell
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramNormalize
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.Subexp.MatrixProgramSupport

def saved (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue backup : List Bool) : State 8 18 :=
  ⟨regs, Function.update (state regs acc (prior,[]) (old,[]) queue).stacks 14 backup⟩

@[simp] theorem saved_nil (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue : List Bool) :
    saved regs acc prior old queue [] = state regs acc (prior,[]) (old,[]) queue := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  by_cases hj : j = 14
  · subst j; simp [ state]
  · simp [ state, hj]

abbrev saveOld : Cmd 8 18 := copy 2 14 13

theorem saveOld_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue : List Bool) :
    ∃ r, Eval saveOld (7*old.length+5)
      (state regs acc (prior,[]) (old,[]) queue)
      (saved r acc prior old queue old) := by
  obtain ⟨e, he, hs⟩ := copy_eval (2 : Fin 18) 14 13
    (by decide) (by decide) (by decide)
    (state regs acc (prior,[]) (old,[]) queue) (by simp [state])
  have hout : e = saved e.regs acc prior old queue old := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs]
    funext j
    fin_cases j <;> simp [ state, StackRoutines.copyStacks]
  rw [hout] at he
  exact ⟨e.regs, by simpa [saveOld, state] using he⟩

abbrev addLocal : Cmd 8 3 :=
  .seq (.base (.atom (.set 0 false))) (.call BinaryPrograms.Add.littleEndianProgram)

def addState (regs : Fin 8 → Bool) (prior old : List Bool) : State 8 3 :=
  ⟨regs, BinaryPrograms.Add.stackState prior old []⟩

theorem addLocal_eval (regs : Fin 8 → Bool) (prior old : List Bool) :
    ∃ t ≤ 16*(max prior.length old.length+1)+1, ∃ r,
      Eval addLocal t (addState regs prior old) (addState r (add prior old) []) := by
  let r₀ := Function.update regs 0 false
  have hs : Eval (.base (.atom (.set 0 false))) 1
      (addState regs prior old) (addState r₀ prior old) := .base (.atom _ _)
  obtain ⟨r,t,ht,he⟩ := BinaryPrograms.Add.littleEndian_run r₀ prior old
  have ha : Eval (.call BinaryPrograms.Add.littleEndianProgram) t
      (addState r₀ prior old) (addState r (add prior old) []) := by
    apply Eval.call
    rw [show BinaryPrograms.Add.littleEndianProgram.entry = 0 from rfl]
    simpa [addState,r₀,add,StructuredProgram.State.withPC,
      BinaryPrograms.Add.littleEndianProgram] using he
  exact ⟨1+t,by omega,r,hs.seq ha⟩

def addPorts : Fin 3 → Fin 18 := ![0,2,4]
theorem addPorts_injective : Function.Injective addPorts := by decide

abbrev addCommand : Cmd 8 18 := liftCommand addLocal 0 0 id addPorts

theorem addCommand_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue backup : List Bool) :
    ∃ t ≤ 16*(max prior.length old.length+1)+2, ∃ r,
      Eval addCommand t (saved regs acc prior old queue backup)
        (saved r acc (add prior old) [] queue backup) := by
  obtain ⟨t,ht,r,he⟩ := addLocal_eval regs prior old
  have hs : embedState id addPorts (saved regs acc prior old queue backup)
      (addState regs prior old) = saved regs acc prior old queue backup := by
    apply embedState_eq_of_ports id addPorts _ _ _ Function.injective_id addPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [addState,addPorts,saved,state,BinaryPrograms.Add.stackState]
    · intro i hi; rfl
  have hf : embedState id addPorts (saved regs acc prior old queue backup)
      (addState r (add prior old) []) = saved r acc (add prior old) [] queue backup := by
    apply embedState_eq_of_ports id addPorts _ _ _ Function.injective_id addPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [addState,addPorts,saved,state,BinaryPrograms.Add.stackState]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [addPorts] using h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨1,by simpa [addPorts] using h.symm⟩
      by_cases h14 : i = 14 <;> simp [saved,state,h0,h2,h14]
  have h := eval_liftCommand he 0 0 id addPorts
    (saved regs acc prior old queue backup) Function.injective_id addPorts_injective
  rw [hs,hf] at h
  exact ⟨t+1,by omega,r,h⟩

theorem emit_saved_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior queue backup : List Bool) :
    ∃ r, Eval cacheEmit (18*prior.length+39)
      (saved regs acc prior [] queue backup)
      (saved r ((LayoutScalarEmitter.record prior []).reverse++acc.1,acc.2)
        prior [] queue backup) := by
  let d := saved regs acc prior [] queue backup
  let a := projectState id cacheEmitPorts d
  have ha : LayoutScalarEmitter.Ready a := by
    simp [LayoutScalarEmitter.Ready,a,d,projectState,cacheEmitPorts,saved,state]
  obtain ⟨e,he,hs⟩ := LayoutScalarEmitter.emitPair_eval a ha
  have h := eval_liftCommand_from_state LayoutScalarEmitter.emitPair 0 2
    id cacheEmitPorts d Function.injective_id cacheEmitPorts_injective he
  have hout : embedState id cacheEmitPorts d e =
      saved e.regs ((LayoutScalarEmitter.record prior []).reverse++acc.1,acc.2)
        prior [] queue backup := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      exact embedState_register id cacheEmitPorts d e Function.injective_id i
    ·
      rw [hs,ProgramLinking.extend_update cacheEmitPorts_injective]
      have hbase := congrArg StructuredProgram.State.stacks
        (embedState_project id cacheEmitPorts d Function.injective_id cacheEmitPorts_injective)
      change Function.extend cacheEmitPorts a.stacks d.stacks = d.stacks at hbase
      rw [hbase]
      funext j
      fin_cases j <;> simp [a,d,projectState,cacheEmitPorts,saved,state]
  refine ⟨e.regs,?_⟩
  rw [hout] at h
  simpa [cacheEmit,a,d,projectState,cacheEmitPorts,saved,state,Nat.add_assoc] using h

abbrev clearCarry : Cmd 8 18 := .call (StackRoutines.clearProgram 0 0 1)

theorem clearCarry_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior queue backup : List Bool) :
    Eval clearCarry (2*prior.length+3)
      (saved regs acc prior [] queue backup)
      (saved (readRegs regs 0 1 none) acc [] [] queue backup) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (0 : Fin 18) (0 : Fin 8) 1
    (saved regs acc prior [] queue backup)
  have hs : StackRoutines.clearStacks 0 (saved regs acc prior [] queue backup).stacks =
      (saved (readRegs regs 0 1 none) acc [] [] queue backup).stacks := by
    funext j
    fin_cases j <;> simp [saved,state,StackRoutines.clearStacks]
  rw [hs] at h
  simpa [clearCarry,saved,state] using h

abbrev restoreOld : Cmd 8 18 := move 14 0 13

theorem restoreOld_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (old queue : List Bool) :
    ∃ r, Eval restoreOld (6*old.length+6)
      (saved regs acc [] [] queue old)
      (state r acc (old,[]) ([],[]) queue) := by
  obtain ⟨e,he,hs⟩ := move_eval (14 : Fin 18) 0 13
    (by decide) (by decide) (by decide) (saved regs acc [] [] queue old)
    (by simp [saved,state]) (by simp [saved,state])
  have hout : e = state e.regs acc (old,[]) ([],[]) queue := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs]
    funext j
    fin_cases j <;> simp [saved,state]
  rw [hout] at he
  exact ⟨e.regs, by simpa [restoreOld,saved,state] using he⟩

abbrev cell : Cmd 8 18 :=
  .seq saveOld (.seq addCommand (.seq cacheEmit (.seq clearCarry restoreOld)))

theorem cell_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue : List Bool) :
    ∃ t ≤ 60*(max prior.length old.length+2), ∃ r,
      Eval cell t (state regs acc (prior,[]) (old,[]) queue)
        (state r ((LayoutScalarEmitter.record (add prior old) []).reverse++acc.1,acc.2)
          (old,[]) ([],[]) queue) := by
  obtain ⟨r₁,h₁⟩ := saveOld_eval regs acc prior old queue
  obtain ⟨ta,hta,r₂,h₂⟩ := addCommand_eval r₁ acc prior old queue old
  obtain ⟨r₃,h₃⟩ := emit_saved_eval r₂ acc (add prior old) queue old
  have h₄ := clearCarry_eval r₃
    ((LayoutScalarEmitter.record (add prior old) []).reverse++acc.1,acc.2)
    (add prior old) queue old
  obtain ⟨r₅,h₅⟩ := restoreOld_eval (readRegs r₃ 0 1 none)
    ((LayoutScalarEmitter.record (add prior old) []).reverse++acc.1,acc.2) old queue
  refine ⟨(7*old.length+5)+(ta+((18*(add prior old).length+39)+
    ((2*(add prior old).length+3)+(6*old.length+6)))),?_,r₅,?_⟩
  · have hl := length_add prior old
    have hm := le_max_right prior.length old.length
    omega
  · exact h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One paid Pascal row pass over the framed cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev row : Cmd 8 18 := .seq parse (.while 7 (.seq cell parse))

theorem row_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (acc : WordPair) (prior : List Bool) (B : ℕ)
    (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 200*(xs.length+1)*(B+4), ∃ r,
      r 7 = false ∧
      Eval row t
        (state regs acc (prior,[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
        (state r ((cacheRecords (scan prior xs)).reverse++acc.1,acc.2)
          (last prior xs,[]) ([],[]) []) := by
  induction xs generalizing regs acc prior with
  | nil =>
    obtain ⟨r,hg,he⟩ := parse_nil regs acc (prior,[])
    refine ⟨4,by simp; omega,r,hg,?_⟩
    simpa [row,scan,last] using he.seq (.while_false hg)
  | cons old xs ih =>
    have ho := hx old (by simp)
    have hxs : ∀ x ∈ xs, x.length ≤ B := by
      intro x h
      exact hx x (by simp [h])
    obtain ⟨r₁,hg₁,hp₁⟩ := parse_cons regs acc (prior,[]) (old,[])
      (xs.map fun x => (x,[]))
    obtain ⟨tc,htc,r₂,hc⟩ := cell_eval r₁ acc prior old
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨tt,htt,r₃,hg₃,ht⟩ := ih r₂
      ((LayoutScalarEmitter.record (add prior old) []).reverse++acc.1,acc.2) old ho hxs
    cases ht with
    | seq hparse hwhile =>
      rename_i tp tw between
      refine ⟨6*pairLength (old,[])+11+(tc+tp+tw+1),?_,r₃,hg₃,?_⟩
      · simp only [pairLength,List.length_nil,Nat.add_zero,List.length_cons] at *
        have hm : max prior.length old.length ≤ B := by omega
        calc
          6 * old.length + 11 + (tc + tp + tw + 1) ≤
              6 * B + 11 + (60 * (B + 2) + 200 * (xs.length + 1) * (B + 4) + 1) := by
            omega
          _ ≤ 200 * (xs.length + 1 + 1) * (B + 4) := by
            ring_nf
            omega
      · have hall := hp₁.seq (.while_true hg₁ (hc.seq hparse) hwhile)
        simpa [row,scan,last,cacheRecords,List.reverse_append,
          List.append_assoc,Nat.add_assoc] using hall

abbrev pass : Cmd 8 18 := .seq row (.seq cacheFinishList cacheClear)

theorem pass_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (counter : List Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 300*(xs.length+1)*(B+4), ∃ r,
      Eval pass t
        (state regs ([],counter) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
        (state r ([],counter) ([],[]) ([],[])
          (pairEncoding ((scan [] xs).map fun x => (x,[])))) := by
  obtain ⟨tr,htr,r₁,_,hr⟩ := row_eval xs regs ([],counter) [] B (by simp) hx
  obtain ⟨r₂,hf⟩ := cacheFinishList_eval r₁
    ((cacheRecords (scan [] xs)).reverse++[],counter) (last [] xs)
  have hc := cacheClear_eval r₂ ([],counter) (last [] xs)
    (((cacheRecords (scan [] xs)).reverse++[]).reverse++[false])
  have hout : ((cacheRecords (scan [] xs)).reverse++[]).reverse++[false] =
      pairEncoding ((scan [] xs).map fun x => (x,[])) := by
    simpa using (cacheRecords_encoding (scan [] xs)).symm
  have hword := scan_word_length [] xs B (by simp) hx
  have hlen := cacheRecords_length_le (scan [] xs) (B+1) hword
  rw [scan_length] at hlen
  have hlast := last_length [] xs B (by simp) hx
  refine ⟨tr+((3*((cacheRecords (scan [] xs)).reverse++[]).length+9)+
      (2*(last [] xs).length+3)),?_,readRegs r₂ 0 1 none,?_⟩
  · simp only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero]
    nlinarith only [htr, hlen, hlast, Nat.zero_le B, Nat.zero_le xs.length]
  · simpa only [hout] using hr.seq (hf.seq hc)

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed while loop consumes the runtime unary iteration count. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev loop : Cmd 8 18 := .while 6 (.seq pass cacheRead)

theorem loop_eval (counter : List Bool) (xs : List (List Bool))
    (regs : Fin 8 → Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 400*(counter.length+1)*(xs.length+1)*(B+counter.length+4),
    ∃ r, Eval loop t (cacheAfterRead regs counter xs)
      (state r ([],[]) ([],[]) ([],[])
        (pairEncoding ((iterate counter.length xs).map fun x => (x,[])))) := by
  induction counter generalizing xs regs B with
  | nil =>
    refine ⟨1,by simp; nlinarith,readRegs regs 7 6 none,?_⟩
    simpa [loop,cacheAfterRead,iterate] using
      (Eval.while_false (test := (6 : Fin 8)) (body := .seq pass cacheRead)
        (a := cacheAfterRead regs [] xs)
        (by simp [cacheAfterRead,state,readRegs_present]))
  | cons bit counter ih =>
    let rr := readRegs regs 7 6 (some bit)
    obtain ⟨tp,htp,rp,hp⟩ := pass_eval xs rr counter B hx
    have hr := cacheRead_eval rp counter (scan [] xs)
    have hscan := scan_word_length [] xs B (by simp) hx
    obtain ⟨tl,htl,rl,hl⟩ := ih (scan [] xs) rp (B+1) hscan
    refine ⟨tp+1+tl+1,?_,rl,?_⟩
    · rw [scan_length] at htl
      simp only [List.length_cons]
      have henv : B+1+counter.length+4 = B+(counter.length+1)+4 := by omega
      rw [henv] at htl
      have he : B+4 ≤ B+(counter.length+1)+4 := by omega
      have hprod := Nat.mul_le_mul_left (300*(xs.length+1)) he
      nlinarith
    · have he := Eval.while_true (test := (6 : Fin 8))
        (by simp [state,rr,readRegs_present]) (hp.seq hr) hl
      simpa [loop,cacheAfterRead,iterate,rr] using he

abbrev command : Cmd 8 18 := .seq cacheRead loop
def program := compiled command 17 15

theorem program_runsIn (counter : List Bool) (xs : List (List Bool))
    (regs : Fin 8 → Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ r, RunsIn program
      (400*(counter.length+1)*(xs.length+1)*(B+counter.length+4)+2)
      ((state regs ([],counter) ([],[]) ([],[])
        (pairEncoding (xs.map fun x => (x,[])))).withPC (some program.entry))
      ((state r ([],[]) ([],[]) ([],[])
        (pairEncoding ((iterate counter.length xs).map fun x => (x,[])))).withPC none) := by
  obtain ⟨t,ht,r,he⟩ := loop_eval counter xs regs B hx
  refine ⟨r,1+t+1,by omega,?_⟩
  exact compiled_halt_trace ((cacheRead_eval regs counter xs).seq he) 17 15

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

private def zeroPorts : UnaryForPrograms.Ports 8 18 := ⟨17,7,6⟩

def zeroRecord : List Bool := [true,false,false]

abbrev zeroBody : Cmd 8 18 := ArithmeticExpressionSupport.pushWord 15 zeroRecord

abbrev zeroCommand : Cmd 8 18 :=
  .seq (ArithmeticExpressionSupport.pushWord 15 [false])
    (UnaryForPrograms.forCmd zeroPorts zeroBody)

theorem zeroRecord_encoding (xs : List WordPair) :
    zeroRecord ++ pairEncoding xs = pairEncoding (([],[])::xs) := rfl

private def ZeroInvariant (base : State 8 18) (i : ℕ) (d : State 8 18) : Prop :=
  d.stacks 15 = pairEncoding (List.replicate i ([],[])) ∧
  ∀ j, j ≠ 15 → j ≠ 17 → d.stacks j = base.stacks j

private theorem zero_stable (base : State 8 18) :
    UnaryForPrograms.FrameStable zeroPorts (ZeroInvariant base) := by
  intro i a b hab hi
  refine ⟨?_,fun j hj hk => (hab j hk).symm.trans (hi.2 j hj hk)⟩
  exact (hab 15 (by decide)).symm.trans hi.1

private theorem zero_body (base : State 8 18) :
    UnaryForPrograms.BodySpec zeroPorts zeroBody (ZeroInvariant base) (fun _ => 6) := by
  intro i d hi
  obtain ⟨r,he⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) zeroRecord d
  refine ⟨6,⟨r,Function.update d.stacks 15 (zeroRecord++d.stacks 15)⟩,le_rfl,he,by simp [zeroPorts],?_,?_⟩
  · simp only [Function.update_same,hi.1,zeroRecord_encoding,List.replicate_succ]
  · intro j hj hk
    simpa [hj] using hi.2 j hj hk

theorem zeroCommand_eval (regs : Fin 8 → Bool) (counter : List Bool) :
    ∃ t ≤ 8*counter.length+4, ∃ r,
      Eval zeroCommand t (state regs ([],counter) ([],[]) ([],[]) [])
        (state r ([],[]) ([],[]) ([],[])
          (pairEncoding (List.replicate counter.length ([],[])))) := by
  let d := state regs ([],counter) ([],[]) ([],[]) []
  obtain ⟨r₀,h₀⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) [false] d
  let a : State 8 18 := ⟨r₀,Function.update d.stacks 15 [false]⟩
  have hi : ZeroInvariant d 0 a := by
    constructor
    · rfl
    · intro j hj _; simp [a,hj]
  obtain ⟨t,e,he,hi',hc,ht⟩ := UnaryForPrograms.for_correct zeroPorts zeroBody
    (ZeroInvariant d) (fun _ => 6) (zero_stable d) (zero_body d) a hi
  have hc' : e.stacks 17 = [] := hc
  have hi'₁ : e.stacks 15 = pairEncoding (List.replicate counter.length ([],[])) := by
    simpa [a,d,state,zeroPorts] using hi'.1
  have heq : e = state e.regs ([],[]) ([],[]) ([],[])
      (pairEncoding (List.replicate counter.length ([],[]))) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    funext j
    by_cases hj : j = 15
    · subst j; exact hi'₁
    by_cases hk : j = 17
    · subst j; exact hc'
    rw [hi'.2 j hj hk]
    simp [d,state,hj,hk]
  refine ⟨2+t,?_,e.regs,?_⟩
  · have ht' : t ≤ counter.length*6+2*counter.length+2 := by
      simpa [a,d,state,zeroPorts,CounterForPrograms.budgetSum_const] using ht
    omega
  · have hh : Eval zeroCommand (2+t) d e := h₀.seq he
    rw [heq] at hh
    simpa only [d] using hh



abbrev initialPop : Cmd 8 18 := .base (.atom (.pop 17 7 6))

theorem initialPop_eval (regs : Fin 8 → Bool) (counter : List Bool) :
    Eval initialPop 1 (state regs ([],counter) ([],[]) ([],[]) [])
      (state (readRegs regs 7 6 counter.head?) ([],counter.tail) ([],[]) ([],[]) []) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (17 : Fin 18) (7 : Fin 8) 6)
    (state regs ([],counter) ([],[]) ([],[]) []))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;> simp [state,StructuredProgram.Atom.instr,
execInstr]

abbrev initialCommand : Cmd 8 18 :=
  .seq initialPop (.ite 6
    (.seq zeroCommand (ArithmeticExpressionSupport.pushWord 15 [true,true,true,false,false]))
    (ArithmeticExpressionSupport.pushWord 15 [false]))

theorem initialCommand_eval (regs : Fin 8 → Bool) (counter : List Bool) :
    ∃ t ≤ 12*counter.length+20, ∃ r,
      Eval initialCommand t (state regs ([],counter) ([],[]) ([],[]) [])
        (state r ([],[]) ([],[]) ([],[])
          (pairEncoding ((initial counter.length).map fun x => (x,[])))) := by
  have hp := initialPop_eval regs counter
  cases counter with
  | nil =>
    obtain ⟨r,hr⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) [false]
      (state (readRegs regs 7 6 none) ([],[]) ([],[]) ([],[]) [])
    have hout : (⟨r,Function.update
        (state (readRegs regs 7 6 none) ([],[]) ([],[]) ([],[]) []).stacks
        15 ([false]++[])⟩ : State 8 18) =
        state r ([],[]) ([],[]) ([],[]) (pairEncoding []) := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j; fin_cases j <;> simp [state,pairEncoding]
    change Eval _ _ _ ⟨r,Function.update
      (state (readRegs regs 7 6 none) ([],[]) ([],[]) ([],[]) []).stacks
      15 ([false]++[])⟩ at hr
    rw [hout] at hr
    refine ⟨4,by simp,r,?_⟩
    simpa [initialCommand] using hp.seq (Eval.ite_false
      (test := (6 : Fin 8)) (by simp [state,readRegs_present]) hr)
  | cons b bs =>
    obtain ⟨t,ht,r,he⟩ := zeroCommand_eval (readRegs regs 7 6 (some b)) bs
    obtain ⟨r',hr⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18)
      [true,true,true,false,false]
      (state r ([],[]) ([],[]) ([],[]) (pairEncoding (List.replicate bs.length ([],[]))))
    have hout : (⟨r',Function.update
        (state r ([],[]) ([],[]) ([],[]) (pairEncoding (List.replicate bs.length ([],[])))).stacks
        15 ([true,true,true,false,false]++pairEncoding (List.replicate bs.length ([],[])))⟩ :
        State 8 18) = state r' ([],[]) ([],[]) ([],[])
        (pairEncoding ((initial (bs.length+1)).map fun x => (x,[]))) := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j; fin_cases j <;> simp [state,initial_succ,pairEncoding,Encoding.frame]
    change Eval _ _ _ ⟨r',Function.update
      (state r ([],[]) ([],[]) ([],[]) (pairEncoding (List.replicate bs.length ([],[])))).stacks
      15 ([true,true,true,false,false]++pairEncoding (List.replicate bs.length ([],[])))⟩ at hr
    rw [hout] at hr
    refine ⟨1+((t+10)+1),by simp only [List.length_cons]; omega,r',?_⟩
    simpa [initialCommand] using hp.seq (Eval.ite_true
      (test := (6 : Fin 8)) (by simp [state,readRegs_present]) (he.seq hr))

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev BuildData := State 8 19

def buildState (regs : Fin 8 → Bool) (a r queue : List Bool) : BuildData :=
  ⟨regs,fun j => if j = 15 then queue else if j = 17 then a else if j = 18 then r else []⟩

def initialBuildPorts (j : Fin 18) : Fin 19 := if j = 17 then 18 else Fin.castAdd 1 j

theorem initialBuildPorts_injective : Function.Injective initialBuildPorts := by decide

def cacheBuildPorts : Fin 18 → Fin 19 := Fin.castAdd 1

theorem cacheBuildPorts_injective : Function.Injective cacheBuildPorts := Fin.castAdd_injective _ _

abbrev initialBuild : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram (compiled initialCommand 17 15) id initialBuildPorts)

abbrev cacheBuildLoop : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram program id cacheBuildPorts)

theorem initialBuild_eval (regs : Fin 8 → Bool) (a r : List Bool) :
    ∃ t ≤ 12*r.length+21, ∃ regs',
      Eval initialBuild t (buildState regs a r [])
        (buildState regs' a [] (pairEncoding (((initial r.length).map fun x => (x,[]))))) := by
  obtain ⟨t,ht,regs',he⟩ := initialCommand_eval regs r
  have hs : embedState id initialBuildPorts (buildState regs a r [])
      (state regs ([],r) ([],[]) ([],[]) []) = buildState regs a r [] := by
    apply embedState_eq_of_ports id initialBuildPorts _ _ _
      Function.injective_id initialBuildPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [buildState,state,initialBuildPorts]
    · intro i hi; rfl
  have hf : embedState id initialBuildPorts (buildState regs a r [])
      (state regs' ([],[]) ([],[]) ([],[])
        (pairEncoding (((initial r.length).map fun x => (x,[]))))) =
      buildState regs' a [] (pairEncoding (((initial r.length).map fun x => (x,[])))) := by
    apply embedState_eq_of_ports id initialBuildPorts _ _ _
      Function.injective_id initialBuildPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [buildState,state,initialBuildPorts]
    · intro i hi
      have hrange : ∀ j : Fin 19, j ≠ 17 → j ∈ Set.range initialBuildPorts := by decide
      have hj : i = 17 := by by_contra h; exact hi (hrange i h)
      subst i
      simp [buildState]
  have h := eval_call_lifted (compiled initialCommand 17 15) id initialBuildPorts
    (buildState regs a r []) Function.injective_id initialBuildPorts_injective
    (compiled_halt_trace he 17 15)
  rw [hs,hf] at h
  exact ⟨t+1,by omega,regs',h⟩

theorem cacheBuildLoop_eval (regs : Fin 8 → Bool) (a : List Bool)
    (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 400*(a.length+1)*(xs.length+1)*(B+a.length+4)+2,
    ∃ regs', Eval cacheBuildLoop t
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (buildState regs' [] [] (pairEncoding ((iterate a.length xs).map fun x => (x,[])))) := by
  obtain ⟨regs',t,ht,he⟩ := program_runsIn a xs regs B hx
  have hs : embedState id cacheBuildPorts
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (state regs ([],a) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[])))) =
      buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))) := by
    apply embedState_eq_of_ports id cacheBuildPorts _ _ _
      Function.injective_id cacheBuildPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [buildState,state,cacheBuildPorts]
    · intro i hi; rfl
  have hf : embedState id cacheBuildPorts
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (state regs' ([],[]) ([],[]) ([],[])
        (pairEncoding ((iterate a.length xs).map fun x => (x,[])))) =
      buildState regs' [] [] (pairEncoding ((iterate a.length xs).map fun x => (x,[]))) := by
    apply embedState_eq_of_ports id cacheBuildPorts _ _ _
      Function.injective_id cacheBuildPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [buildState,state,cacheBuildPorts]
    · intro i hi
      have hrange : ∀ j : Fin 19, j ≠ 18 → j ∈ Set.range cacheBuildPorts := by decide
      have hj : i = 18 := by by_contra h; exact hi (hrange i h)
      subst i
      simp [buildState]
  have h := eval_call_lifted program id cacheBuildPorts
    (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
    Function.injective_id cacheBuildPorts_injective he
  rw [hs,hf] at h
  exact ⟨t,ht,regs',h⟩

abbrev buildCommand : Cmd 8 19 := .seq initialBuild cacheBuildLoop
def buildProgram := compiled buildCommand 17 15

theorem buildProgram_runsIn (regs : Fin 8 → Bool) (a r : List Bool) :
    ∃ (regs' : Fin 8 → Bool) (xs : List (List Bool)),
      RunsIn buildProgram
        (12*r.length+400*(a.length+1)*(r.length+1)*(a.length+5)+24)
        ((buildState regs a r []).withPC (some buildProgram.entry))
        ((buildState regs' [] [] (pairEncoding (xs.map fun x => (x,[])))).withPC none) ∧
      xs.length = r.length ∧
      xs.map BinaryArithmetic.toNat = (List.range r.length).map (Nat.choose a.length) ∧
      (∀ x ∈ xs, x.length ≤ a.length+1) := by
  obtain ⟨ti,hti,ri,hi⟩ := initialBuild_eval regs a r
  have hw : ∀ x ∈ initial r.length, x.length ≤ 1 := initial_word_length r.length
  obtain ⟨tc,htc,rc,hc⟩ := cacheBuildLoop_eval ri a (initial r.length) 1 hw
  refine ⟨rc,iterate a.length (initial r.length),
    ⟨ti+tc+1,?_,compiled_halt_trace (hi.seq hc) 17 15⟩,?_,?_,?_⟩
  · simp only [initial_length] at htc
    have he : 1+a.length+4 = a.length+5 := by omega
    rw [he] at htc
    omega
  · simp
  · exact iterate_initial_values a.length r.length
  · exact iterate_initial_word_length a.length r.length

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.LayoutProgram

abbrev NormalizeData := State 8 9

def normalizeState (regs : Fin 8 → Bool) (word width buffer : List Bool) : NormalizeData :=
  ⟨regs,![word,width,buffer,[],[],[],[],[],[]]⟩

def normalizePorts : Fin 8 ↪ Fin 9 :=
  ⟨![0,4,5,6,7,2,8,3],by decide⟩

abbrev normalizeComponent : Cmd 8 9 :=
  .seq (copy 1 3 4) (.seq (normalizeAt normalizePorts) (transfer 0 2))

theorem normalizeComponent_eval (regs : Fin 8 → Bool) (word width buffer : List Bool) :
    ∃ t ≤ 17*width.length+2*word.length+17, ∃ r,
      Eval normalizeComponent t (normalizeState regs word width buffer)
        (normalizeState r [] width ((ModularArithmetic.padTo width word).reverse++buffer)) := by
  let d := normalizeState regs word width buffer
  obtain ⟨a,ha,hsa⟩ := copy_eval (1 : Fin 9) 3 4
    (by decide) (by decide) (by decide) d (by simp [d,normalizeState])
  have has : a.stacks = ![word,width,buffer,width,[],[],[],[],[]] := by
    rw [hsa]
    funext j; fin_cases j <;> simp [d,normalizeState,StackRoutines.copyStacks]
  have har : normalizeReady normalizePorts a := by
    intro i h0 h5 h7
    fin_cases i <;> simp [normalizePorts,has] at h0 h5 h7 ⊢
  obtain ⟨tn,htn,rn,hn⟩ := normalizeAt_eval normalizePorts a har
  let b : NormalizeData := ⟨rn,normalizedStacks normalizePorts a⟩
  have hbs : b.stacks = ![ModularArithmetic.padTo width word,width,buffer,[],[],[],[],[],[]] := by
    funext j; fin_cases j <;> simp [b,normalizedStacks,normalizePorts,has]
  obtain ⟨e,he,hse⟩ := transfer_eval (0 : Fin 9) 2 (by decide) b
  have hout : e = normalizeState e.regs [] width
      ((ModularArithmetic.padTo width word).reverse++buffer) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hse,hbs]
    funext j; fin_cases j <;> simp [StackRoutines.transferStacks]
  rw [hout] at he
  refine ⟨(7*width.length+5)+(tn+(3*width.length+3)),?_,e.regs,?_⟩
  · simp [normalizePorts,has] at htn
    omega
  · have hb0 : (b.stacks 0).length = width.length := by
      rw [hbs]
      exact ModularArithmetic.padTo_length width word
    have hh := ha.seq (hn.seq he)
    simpa [normalizeComponent,d,normalizeState,hb0] using hh

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev FlatData := State 8 19

def wide (width : List Bool) (d : State 8 18) : FlatData :=
  ⟨d.regs,fun j => if h : j.val < 18 then d.stacks ⟨j.val,h⟩ else width⟩

def flatState (regs : Fin 8 → Bool) (width : List Bool)
    (acc work next : WordPair) (queue : List Bool) : FlatData :=
  wide width (state regs acc work next queue)

def basePorts : Fin 18 → Fin 19 := Fin.castAdd 1

theorem basePorts_injective : Function.Injective basePorts := Fin.castAdd_injective _ _

theorem embed_wide (width : List Bool) (a b : State 8 18) :
    embedState id basePorts (wide width a) b = wide width b := by
  apply embedState_eq_of_ports id basePorts _ _ _ Function.injective_id basePorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; simp [wide,basePorts]
  · intro i hi
    have hh : ¬i.val < 18 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,by apply Fin.ext; rfl⟩
    simp [wide,hh]

theorem wide_eval {c : Cmd 8 18} {n : ℕ} {a b : State 8 18}
    (h : Eval c n a b) (width : List Bool) :
    Eval (liftCommand c 15 15 id basePorts) (n+1) (wide width a) (wide width b) := by
  have hh := eval_liftCommand h 15 15 id basePorts (wide width a)
    Function.injective_id basePorts_injective
  simpa only [embed_wide] using hh

abbrev flatParse : Cmd 8 19 := liftCommand parse 15 15 id basePorts

def positivePorts : Fin 9 → Fin 19 := ![2,18,16,4,5,6,7,8,9]
def negativePorts : Fin 9 → Fin 19 := ![3,18,17,4,5,6,7,8,9]

theorem positivePorts_injective : Function.Injective positivePorts := by decide
theorem negativePorts_injective : Function.Injective negativePorts := by decide

abbrev flatPositive : Cmd 8 19 := liftCommand normalizeComponent 0 2 id positivePorts
abbrev flatNegative : Cmd 8 19 := liftCommand normalizeComponent 0 2 id negativePorts

theorem flatPositive_eval (regs : Fin 8 → Bool) (width : List Bool)
    (acc : WordPair) (positive negative queue : List Bool) :
    ∃ t ≤ 17*width.length+2*positive.length+18, ∃ r,
      Eval flatPositive t (flatState regs width acc ([],[]) (positive,negative) queue)
        (flatState r width ((ModularArithmetic.padTo width positive).reverse++acc.1,acc.2)
          ([],[]) ([],negative) queue) := by
  obtain ⟨t,ht,r,he⟩ := normalizeComponent_eval regs positive width acc.1
  have hs : embedState id positivePorts
      (flatState regs width acc ([],[]) (positive,negative) queue)
      (normalizeState regs positive width acc.1) =
      flatState regs width acc ([],[]) (positive,negative) queue := by
    apply embedState_eq_of_ports id positivePorts _ _ _
      Function.injective_id positivePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [flatState,wide,state,positivePorts,normalizeState]
    · intro i hi; rfl
  have hf : embedState id positivePorts
      (flatState regs width acc ([],[]) (positive,negative) queue)
      (normalizeState r [] width ((ModularArithmetic.padTo width positive).reverse++acc.1)) =
      flatState r width ((ModularArithmetic.padTo width positive).reverse++acc.1,acc.2)
        ([],[]) ([],negative) queue := by
    apply embedState_eq_of_ports id positivePorts _ _ _
      Function.injective_id positivePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [flatState,wide,state,positivePorts,normalizeState]
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨0,by simpa [positivePorts] using h.symm⟩
      have h16 : i ≠ 16 := fun h => hi ⟨2,by simpa [positivePorts] using h.symm⟩
      fin_cases i <;> simp [flatState,wide,state] at h2 h16 ⊢
  have hh := eval_liftCommand he 0 2 id positivePorts
    (flatState regs width acc ([],[]) (positive,negative) queue)
    Function.injective_id positivePorts_injective
  rw [hs,hf] at hh
  exact ⟨t+1,by omega,r,hh⟩

theorem flatNegative_eval (regs : Fin 8 → Bool) (width : List Bool)
    (acc : WordPair) (negative queue : List Bool) :
    ∃ t ≤ 17*width.length+2*negative.length+18, ∃ r,
      Eval flatNegative t (flatState regs width acc ([],[]) ([],negative) queue)
        (flatState r width (acc.1,(ModularArithmetic.padTo width negative).reverse++acc.2)
          ([],[]) ([],[]) queue) := by
  obtain ⟨t,ht,r,he⟩ := normalizeComponent_eval regs negative width acc.2
  have hs : embedState id negativePorts
      (flatState regs width acc ([],[]) ([],negative) queue)
      (normalizeState regs negative width acc.2) =
      flatState regs width acc ([],[]) ([],negative) queue := by
    apply embedState_eq_of_ports id negativePorts _ _ _
      Function.injective_id negativePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [flatState,wide,state,negativePorts,normalizeState]
    · intro i hi; rfl
  have hf : embedState id negativePorts
      (flatState regs width acc ([],[]) ([],negative) queue)
      (normalizeState r [] width ((ModularArithmetic.padTo width negative).reverse++acc.2)) =
      flatState r width (acc.1,(ModularArithmetic.padTo width negative).reverse++acc.2)
        ([],[]) ([],[]) queue := by
    apply embedState_eq_of_ports id negativePorts _ _ _
      Function.injective_id negativePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [flatState,wide,state,negativePorts,normalizeState]
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨0,by simpa [negativePorts] using h.symm⟩
      have h17 : i ≠ 17 := fun h => hi ⟨2,by simpa [negativePorts] using h.symm⟩
      fin_cases i <;> simp [flatState,wide,state] at h3 h17 ⊢
  have hh := eval_liftCommand he 0 2 id negativePorts
    (flatState regs width acc ([],[]) ([],negative) queue)
    Function.injective_id negativePorts_injective
  rw [hs,hf] at hh
  exact ⟨t+1,by omega,r,hh⟩

def flatWords (width : List Bool) (xs : List (List Bool)) : List Bool :=
  xs.flatMap (ModularArithmetic.padTo width)

def flatZeros (width : List Bool) (xs : List (List Bool)) : List Bool :=
  xs.flatMap (fun _ => ModularArithmetic.padTo width [])

abbrev flatRow : Cmd 8 19 :=
  .seq flatParse (.while 7 (.seq flatPositive (.seq flatNegative flatParse)))

theorem flatRow_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (width : List Bool) (acc : WordPair) (B : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 100*(xs.length+1)*(width.length+B+4), ∃ r,
      r 7 = false ∧
      Eval flatRow t
        (flatState regs width acc ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
        (flatState r width ((flatWords width xs).reverse++acc.1,
          (flatZeros width xs).reverse++acc.2) ([],[]) ([],[]) []) := by
  induction xs generalizing regs acc with
  | nil =>
    obtain ⟨r,hg,he⟩ := parse_nil regs acc ([],[])
    have hh := wide_eval he width
    refine ⟨5,by simp; omega,r,hg,?_⟩
    simpa [flatRow,flatParse,flatState,flatWords,flatZeros] using hh.seq (.while_false hg)
  | cons x xs ih =>
    have hx0 := hx x (by simp)
    obtain ⟨r₁,hg₁,hp₁⟩ := parse_cons regs acc ([],[]) (x,[]) (xs.map fun x => (x,[]))
    have hp := wide_eval hp₁ width
    obtain ⟨tp,htp,r₂,hp₂⟩ := flatPositive_eval r₁ width acc x []
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨tn,htn,r₃,hn₃⟩ := flatNegative_eval r₂ width
      ((ModularArithmetic.padTo width x).reverse++acc.1,acc.2) []
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨tt,htt,r₄,hg₄,ht⟩ := ih r₃
      ((ModularArithmetic.padTo width x).reverse++acc.1,
        (ModularArithmetic.padTo width []).reverse++acc.2)
      (fun y hy => hx y (by simp [hy]))
    cases ht with
    | seq hparse hwhile =>
      rename_i tparse twhile between
      refine ⟨(6*pairLength (x,[])+12)+(tp+tn+tparse+twhile+1),?_,r₄,hg₄,?_⟩
      · simp only [pairLength,List.length_nil,Nat.add_zero,List.length_cons] at *
        nlinarith only [htp, htn, htt, hx0, Nat.zero_le B, Nat.zero_le xs.length,
          Nat.zero_le width.length, Nat.zero_le x.length]
      · have hh := hp.seq (.while_true hg₁ (hp₂.seq (hn₃.seq hparse)) hwhile)
        simpa [flatRow,flatParse,flatState,flatWords,flatZeros,List.flatMap_cons,
          List.reverse_append,List.append_assoc,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

@[simp] theorem flatWords_length (width : List Bool) (xs : List (List Bool)) :
    (flatWords width xs).length = xs.length*width.length := by
  induction xs with
  | nil => simp [flatWords]
  | cons x xs ih =>
    change (ModularArithmetic.padTo width x ++ flatWords width xs).length = _
    simp only [List.length_append,ModularArithmetic.padTo_length,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

@[simp] theorem flatZeros_length (width : List Bool) (xs : List (List Bool)) :
    (flatZeros width xs).length = xs.length*width.length := by
  induction xs with
  | nil => simp [flatZeros]
  | cons x xs ih =>
    change (ModularArithmetic.padTo width [] ++ flatZeros width xs).length = _
    simp only [List.length_append,ModularArithmetic.padTo_length,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

abbrev flatFinish : Cmd 8 19 := .seq (transfer 16 0) (transfer 17 1)

theorem flatFinish_eval (regs : Fin 8 → Bool) (width positive negative : List Bool) :
    ∃ r, Eval flatFinish (3*positive.length+3*negative.length+6)
      (flatState regs width (positive,negative) ([],[]) ([],[]) [])
      (flatState r width ([],[]) (positive.reverse,negative.reverse) ([],[]) []) := by
  let d := flatState regs width (positive,negative) ([],[]) ([],[]) []
  obtain ⟨a,ha,hsa⟩ := transfer_eval (16 : Fin 19) 0 (by decide) d
  obtain ⟨b,hb,hsb⟩ := transfer_eval (17 : Fin 19) 1 (by decide) a
  have han : a.stacks 17 = negative := by
    rw [hsa]; simp [d,flatState,wide,state,StackRoutines.transferStacks]
  have hout : b = flatState b.regs width ([],[]) (positive.reverse,negative.reverse) ([],[]) [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hsb,hsa]
    funext j
    fin_cases j <;> simp [d,flatState,wide,state,StackRoutines.transferStacks]
  rw [hout] at hb
  refine ⟨b.regs,?_⟩
  have hh := ha.seq hb
  have htime : (3*(d.stacks 16).length+3)+(3*(a.stacks 17).length+3) =
      3*positive.length+3*negative.length+6 := by
    simp only [han]
    have hd : d.stacks 16 = positive := by simp [d,flatState,wide,state]
    rw [hd]
    omega
  rw [htime] at hh
  simpa only [flatFinish,d] using hh

abbrev flatCommand : Cmd 8 19 := .seq flatRow flatFinish
def flatProgram := compiled flatCommand 15 0

theorem flatProgram_runsIn (regs : Fin 8 → Bool) (width : List Bool)
    (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ r, RunsIn flatProgram (110*(xs.length+1)*(width.length+B+4)+7)
      ((flatState regs width ([],[]) ([],[]) ([],[])
        (pairEncoding (xs.map fun x => (x,[])))).withPC (some flatProgram.entry))
      ((flatState r width ([],[]) (flatWords width xs,flatZeros width xs) ([],[]) []).withPC none) := by
  obtain ⟨tr,htr,rr,_,hr⟩ := flatRow_eval xs regs width ([],[]) B hx
  obtain ⟨rf,hf⟩ := flatFinish_eval rr width (flatWords width xs).reverse (flatZeros width xs).reverse
  simp only [List.append_nil] at hr
  simp only [List.reverse_reverse,List.length_reverse,flatWords_length,flatZeros_length] at hf
  refine ⟨rf,tr+(3*(xs.length*width.length)+3*(xs.length*width.length)+6)+1,?_,?_⟩
  · nlinarith only [htr, Nat.zero_le B, Nat.zero_le xs.length, Nat.zero_le width.length]
  · exact compiled_halt_trace (hr.seq hf) 15 0

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Value and shape contracts for the generic adapter and binomial row. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BinaryArithmetic

def normalizedWords (width : List Bool) (xs : List (List Bool)) : List (List Bool) :=
  xs.map (ModularArithmetic.padTo width)

@[simp] theorem normalizedWords_length (width : List Bool) (xs : List (List Bool)) :
    (normalizedWords width xs).length = xs.length := by simp [normalizedWords]

theorem normalizedWords_word_length (width : List Bool) (xs : List (List Bool)) :
    ∀ x ∈ normalizedWords width xs, x.length = width.length := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
  exact ModularArithmetic.padTo_length width y

theorem normalizedWords_values (width : List Bool) (xs : List (List Bool))
    (hx : ∀ x ∈ xs, x.length ≤ width.length) :
    (normalizedWords width xs).map BinaryArithmetic.toNat = xs.map BinaryArithmetic.toNat := by
  rw [normalizedWords,List.map_map]
  apply List.map_congr_left
  intro x hx'
  exact ModularArithmetic.padTo_correct width x (hx x hx')

theorem flatWords_eq_flatten (width : List Bool) (xs : List (List Bool)) :
    flatWords width xs = (normalizedWords width xs).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ModularArithmetic.padTo width x ++ flatWords width xs =
      ModularArithmetic.padTo width x ++ (normalizedWords width xs).flatten
    rw [ih]

theorem padTo_nil (width : List Bool) :
    ModularArithmetic.padTo width [] = List.replicate width.length false := by
  induction width with
  | nil => rfl
  | cons b width ih => simp [ModularArithmetic.padTo,ih,List.replicate_succ]

theorem flatZeros_eq (width : List Bool) (xs : List (List Bool)) :
    flatZeros width xs = List.replicate (xs.length*width.length) false := by
  induction xs with
  | nil => simp [flatZeros]
  | cons x xs ih =>
    change ModularArithmetic.padTo width [] ++ flatZeros width xs = _
    rw [padTo_nil,ih]
    rw [List.length_cons]
    have hn : (xs.length+1)*width.length = width.length+xs.length*width.length := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    rw [hn,List.replicate_add]

theorem binomial_normalized_values (h R : ℕ) (width : List Bool)
    (hw : h+1 ≤ width.length) :
    (normalizedWords width (iterate h (initial R))).map BinaryArithmetic.toNat =
      (List.range R).map h.choose := by
  rw [normalizedWords_values width _ (fun x hx =>
    (iterate_initial_word_length h R x hx).trans hw)]
  exact iterate_initial_values h R

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev FinalData := State 8 20

def finalState (regs : Fin 8 → Bool) (h r width queue positive negative : List Bool) : FinalData :=
  ⟨regs,fun j => if j=0 then positive else if j=1 then negative else
    if j=15 then queue else if j=17 then h else if j=18 then r else if j=19 then width else []⟩

def buildFinalPorts : Fin 19 → Fin 20 := Fin.castAdd 1

def flatFinalPorts (j : Fin 19) : Fin 20 :=
  if j=18 then 19 else Fin.castAdd 1 j

theorem buildFinalPorts_injective : Function.Injective buildFinalPorts := Fin.castAdd_injective _ _
theorem flatFinalPorts_injective : Function.Injective flatFinalPorts := by decide

abbrev finalBuild : Cmd 8 20 := .call (ProgramLinking.liftProgram buildProgram id buildFinalPorts)
abbrev finalFlatten : Cmd 8 20 := .call (ProgramLinking.liftProgram flatProgram id flatFinalPorts)

theorem finalBuild_eval (regs : Fin 8 → Bool) (h r width : List Bool) :
    ∃ t ≤ 12*r.length+400*(h.length+1)*(r.length+1)*(h.length+5)+24,
    ∃ (regs' : Fin 8 → Bool) (xs : List (List Bool)), Eval finalBuild t (finalState regs h r width [] [] [])
      (finalState regs' [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] []) ∧
      xs.length=r.length ∧ xs.map BinaryArithmetic.toNat=(List.range r.length).map h.length.choose ∧
      (∀ x ∈ xs, x.length ≤ h.length+1) := by
  obtain ⟨rf,xs,⟨t,ht,he⟩,hlen,hval,hw⟩ := buildProgram_runsIn regs h r
  have hs : embedState id buildFinalPorts (finalState regs h r width [] [] [])
      (buildState regs h r []) = finalState regs h r width [] [] [] := by
    apply embedState_eq_of_ports id buildFinalPorts _ _ _ Function.injective_id buildFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,buildState,buildFinalPorts]
    · intro i hi; rfl
  have hf : embedState id buildFinalPorts (finalState regs h r width [] [] [])
      (buildState rf [] [] (pairEncoding (xs.map fun x => (x,[])))) =
      finalState rf [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [] := by
    apply embedState_eq_of_ports id buildFinalPorts _ _ _ Function.injective_id buildFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,buildState,buildFinalPorts]
    · intro i hi
      have hrange : ∀ j : Fin 20, j≠19 → j∈Set.range buildFinalPorts := by decide
      have hj : i=19 := by
        by_contra hn
        exact hi (hrange i hn)
      subst i; simp [finalState]
  have hh := eval_call_lifted buildProgram id buildFinalPorts
    (finalState regs h r width [] [] []) Function.injective_id buildFinalPorts_injective he
  rw [hs,hf] at hh
  exact ⟨t,ht,rf,xs,hh,hlen,hval,hw⟩

theorem finalFlatten_eval (regs : Fin 8 → Bool) (width : List Bool)
    (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 110*(xs.length+1)*(width.length+B+4)+7, ∃ regs',
      Eval finalFlatten t
        (finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [])
        (finalState regs' [] [] width [] (flatWords width xs) (flatZeros width xs)) := by
  obtain ⟨rf,t,ht,he⟩ := flatProgram_runsIn regs width xs B hx
  have hs : embedState id flatFinalPorts
      (finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [])
      (flatState regs width ([],[]) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[])))) =
      finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [] := by
    apply embedState_eq_of_ports id flatFinalPorts _ _ _ Function.injective_id flatFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,flatState,wide,LayoutProgramScalar.state,flatFinalPorts]
    · intro i hi; rfl
  have hf : embedState id flatFinalPorts
      (finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [])
      (flatState rf width ([],[]) (flatWords width xs,flatZeros width xs) ([],[]) []) =
      finalState rf [] [] width [] (flatWords width xs) (flatZeros width xs) := by
    apply embedState_eq_of_ports id flatFinalPorts _ _ _ Function.injective_id flatFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,flatState,wide,LayoutProgramScalar.state,flatFinalPorts]
    · intro i hi
      have hrange : ∀ j : Fin 20, j≠18 → j∈Set.range flatFinalPorts := by decide
      have hj : i=18 := by
        by_contra hn
        exact hi (hrange i hn)
      subst i; simp [finalState]
  have hh := eval_call_lifted flatProgram id flatFinalPorts
    (finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [])
    Function.injective_id flatFinalPorts_injective he
  rw [hs,hf] at hh
  exact ⟨t,ht,rf,hh⟩

abbrev finalCommand : Cmd 8 20 := .seq finalBuild finalFlatten
def finalProgram := compiled finalCommand 17 0

theorem finalProgram_runsIn (regs : Fin 8 → Bool) (h r width : List Bool)
    (hw : h.length+1 ≤ width.length) :
    ∃ (regs' : Fin 8 → Bool) (words : List (List Bool)),
      RunsIn finalProgram
        (12*r.length+400*(h.length+1)*(r.length+1)*(h.length+5)+
          110*(r.length+1)*(width.length+(h.length+1)+4)+32)
        ((finalState regs h r width [] [] []).withPC (some finalProgram.entry))
        ((finalState regs' [] [] width [] words.flatten
          (List.replicate (r.length*width.length) false)).withPC none) ∧
      words.length=r.length ∧ (∀ x∈words, x.length=width.length) ∧
      words.map BinaryArithmetic.toNat=(List.range r.length).map h.length.choose := by
  obtain ⟨tb,htb,rb,xs,hb,hlen,hval,hxs⟩ := finalBuild_eval regs h r width
  obtain ⟨tf,htf,rf,hf⟩ := finalFlatten_eval rb width xs (h.length+1) hxs
  rw [hlen] at htf
  have hvalue : (normalizedWords width xs).map BinaryArithmetic.toNat=
      (List.range r.length).map h.length.choose := by
    rw [normalizedWords_values width xs (fun x hx => (hxs x hx).trans hw),hval]
  refine ⟨rf,normalizedWords width xs,?_,by simpa using hlen,
    normalizedWords_word_length width xs,hvalue⟩
  refine ⟨tb+tf+1,by omega,?_⟩
  have hh := compiled_halt_trace (hb.seq hf) 17 0
  simpa only [finalProgram,finalCommand,flatWords_eq_flatten,flatZeros_eq,hlen] using hh

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
