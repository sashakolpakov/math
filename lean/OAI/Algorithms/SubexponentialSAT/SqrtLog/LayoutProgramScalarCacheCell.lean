import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar
import OAI.Algorithms.SubexponentialSAT.BinaryPrograms
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrenceScan
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheWord (prior old : List Bool) : List Bool := add (false::prior) old

theorem cacheWord_value (prior old : List Bool) :
    BinaryArithmetic.toNat (cacheWord prior old) = 2*BinaryArithmetic.toNat prior+BinaryArithmetic.toNat old := by
  simp [cacheWord,toNat_add,BinaryArithmetic.toNat,bitVal]

theorem cacheWord_length (prior old : List Bool) :
    (cacheWord prior old).length ≤ max prior.length old.length+2 := by
  have h := length_add (false::prior) old
  dsimp [cacheWord]
  simp only [List.length_cons] at h
  omega

abbrev cacheCellLocal : Cmd 8 3 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 0 0))) (.call BinaryPrograms.Add.littleEndianProgram))

def cacheCellState (regs : Fin 8 → Bool) (prior old : List Bool) : State 8 3 :=
  ⟨regs,BinaryPrograms.Add.stackState prior old []⟩

theorem cacheCellLocal_eval (regs : Fin 8 → Bool) (prior old : List Bool) :
    ∃ t ≤ 16*(max prior.length old.length+2)+2, ∃ r,
      Eval cacheCellLocal t (cacheCellState regs prior old)
        (cacheCellState r (cacheWord prior old) []) := by
  let r₀ := Function.update regs 0 false
  have hs : Eval (.base (.atom (.set 0 false))) 1
      (cacheCellState regs prior old) (cacheCellState r₀ prior old) := .base (.atom _ _)
  have hp : Eval (.base (.atom (.push 0 0))) 1
      (cacheCellState r₀ prior old) (cacheCellState r₀ (false::prior) old) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.push (0 : Fin 3) (0 : Fin 8))
      (cacheCellState r₀ prior old))) using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [cacheCellState,r₀,BinaryPrograms.Add.stackState,StructuredProgram.Atom.instr,execInstr]
  obtain ⟨r,t,ht,he⟩ := BinaryPrograms.Add.littleEndian_run r₀ (false::prior) old
  have ha : Eval (.call BinaryPrograms.Add.littleEndianProgram) t
      (cacheCellState r₀ (false::prior) old)
      (cacheCellState r (cacheWord prior old) []) := by
    apply Eval.call
    rw [show BinaryPrograms.Add.littleEndianProgram.entry = 0 from rfl]
    simpa [cacheCellState,cacheWord,r₀,add,
      StructuredProgram.State.withPC,BinaryPrograms.Add.littleEndianProgram] using he
  refine ⟨1+(1+t),?_,r,hs.seq (hp.seq ha)⟩
  simp only [List.length_cons] at ht
  omega

def cacheCellPorts : Fin 3 → Fin 18 := ![0,2,4]

theorem cacheCellPorts_injective : Function.Injective cacheCellPorts := by decide

abbrev cacheCell : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram (compiled cacheCellLocal 0 0) id cacheCellPorts)

theorem cacheCell_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue : List Bool) :
    ∃ t ≤ 16*(max prior.length old.length+2)+3, ∃ r,
      Eval cacheCell t (state regs acc (prior,[]) (old,[]) queue)
        (state r acc (cacheWord prior old,[]) ([],[]) queue) := by
  obtain ⟨t,ht,r,he⟩ := cacheCellLocal_eval regs prior old
  have hs : embedState id cacheCellPorts (state regs acc (prior,[]) (old,[]) queue)
      (cacheCellState regs prior old) = state regs acc (prior,[]) (old,[]) queue := by
    apply embedState_eq_of_ports id cacheCellPorts _ _ _
      Function.injective_id cacheCellPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [cacheCellState,cacheCellPorts,state,BinaryPrograms.Add.stackState]
    · intro i hi; rfl
  have hf : embedState id cacheCellPorts (state regs acc (prior,[]) (old,[]) queue)
      (cacheCellState r (cacheWord prior old) []) =
      state r acc (cacheWord prior old,[]) ([],[]) queue := by
    apply embedState_eq_of_ports id cacheCellPorts _ _ _
      Function.injective_id cacheCellPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [cacheCellState,cacheCellPorts,state,BinaryPrograms.Add.stackState]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [cacheCellPorts] using h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨1,by simpa [cacheCellPorts] using h.symm⟩
      simp [state,h0,h2]
  have h := eval_call_lifted (compiled cacheCellLocal 0 0) id cacheCellPorts
    (state regs acc (prior,[]) (old,[]) queue) Function.injective_id cacheCellPorts_injective
    (compiled_halt_trace he 0 0)
  rw [hs,hf] at h
  exact ⟨t+1,by omega,r,h⟩

def cacheScan : List Bool → List (List Bool) → List (List Bool)
  | _, [] => []
  | prior, old::rest => let next := cacheWord prior old; next::cacheScan next rest

@[simp] theorem cacheScan_length (prior : List Bool) (xs : List (List Bool)) :
    (cacheScan prior xs).length = xs.length := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp [cacheScan,ih]

theorem cacheScan_word_length (prior : List Bool) (xs : List (List Bool))
    (B : ℕ) (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ cacheScan prior xs, x.length ≤ B+2*xs.length := by
  induction xs generalizing prior B with
  | nil => simp [cacheScan]
  | cons old rest ih =>
    have ho := hx old (by simp)
    have hn : (cacheWord prior old).length ≤ B+2 :=
      (cacheWord_length prior old).trans (by omega)
    have hrest : ∀ x ∈ rest, x.length ≤ B+2 := by
      intro x h
      have hh := hx x (by simp [h])
      omega
    have ht := ih (cacheWord prior old) (B+2) hn hrest
    intro x h
    simp only [cacheScan,List.mem_cons] at h
    rcases h with rfl | h
    · simp only [List.length_cons]; omega
    · have hh := ht x h
      simp only [List.length_cons]; omega

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheEmitPorts : Fin 7 → Fin 18 := ![0,1,16,5,6,7,8]
theorem cacheEmitPorts_injective : Function.Injective cacheEmitPorts := by decide

abbrev cacheEmit : Cmd 8 18 :=
  liftCommand LayoutScalarEmitter.emitPair 0 2 id cacheEmitPorts

theorem cacheEmit_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior queue : List Bool) :
    ∃ r, Eval cacheEmit (18*prior.length+39)
      (state regs acc (prior,[]) ([],[]) queue)
      (state r ((LayoutScalarEmitter.record prior []).reverse++acc.1,acc.2)
        (prior,[]) ([],[]) queue) := by
  let d := state regs acc (prior,[]) ([],[]) queue
  let a := projectState id cacheEmitPorts d
  have ha : LayoutScalarEmitter.Ready a := by
    simp [LayoutScalarEmitter.Ready,a,d,projectState,cacheEmitPorts,state]
  obtain ⟨e,he,hs⟩ := LayoutScalarEmitter.emitPair_eval a ha
  have h := eval_liftCommand_from_state LayoutScalarEmitter.emitPair 0 2
    id cacheEmitPorts d Function.injective_id cacheEmitPorts_injective he
  have hout : embedState id cacheEmitPorts d e =
      state e.regs ((LayoutScalarEmitter.record prior []).reverse++acc.1,acc.2)
        (prior,[]) ([],[]) queue := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      exact embedState_register id cacheEmitPorts d e Function.injective_id i
    · rw [hs,ProgramLinking.extend_update cacheEmitPorts_injective]
      have hbase := congrArg StructuredProgram.State.stacks
        (embedState_project id cacheEmitPorts d Function.injective_id cacheEmitPorts_injective)
      change Function.extend cacheEmitPorts a.stacks d.stacks = d.stacks at hbase
      rw [hbase]
      funext j
      fin_cases j <;> simp [a,d,projectState,cacheEmitPorts,state]
  refine ⟨e.regs,?_⟩
  rw [hout] at h
  simpa [cacheEmit,a,d,projectState,cacheEmitPorts,state,Nat.add_assoc] using h

def cacheLast : List Bool → List (List Bool) → List Bool
  | prior, [] => prior
  | prior, old::rest => cacheLast (cacheWord prior old) rest

def cacheRecords (xs : List (List Bool)) : List Bool :=
  xs.flatMap fun x => LayoutScalarEmitter.record x []

@[simp] theorem cacheRecords_nil : cacheRecords [] = [] := rfl
@[simp] theorem cacheRecords_cons (x : List Bool) (xs : List (List Bool)) :
    cacheRecords (x::xs) = LayoutScalarEmitter.record x []++cacheRecords xs := rfl

theorem cacheRecords_encoding (xs : List (List Bool)) :
    pairEncoding (xs.map fun x => (x,[])) = cacheRecords xs++[false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [pairEncoding,cacheRecords,LayoutScalarEmitter.record,
      RowSelectionProgram.Entries.pairPrefix,ih,List.append_assoc]

abbrev cacheRow : Cmd 8 18 :=
  .seq parse (.while 7 (.seq cacheCell (.seq cacheEmit parse)))

theorem cacheRow_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (acc : WordPair) (prior : List Bool) (B : ℕ)
    (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 200*(xs.length+1)*(B+2*xs.length+4), ∃ r,
      r 7 = false ∧
      Eval cacheRow t
        (state regs acc (prior,[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
        (state r ((cacheRecords (cacheScan prior xs)).reverse++acc.1,acc.2)
          (cacheLast prior xs,[]) ([],[]) []) := by
  induction xs generalizing regs acc prior B with
  | nil =>
    obtain ⟨r,hg,he⟩ := parse_nil regs acc (prior,[])
    refine ⟨4,by simp; omega,r,hg,?_⟩
    simpa [cacheRow,cacheScan,cacheLast] using he.seq (.while_false hg)
  | cons old xs ih =>
    have ho := hx old (by simp)
    have hn : (cacheWord prior old).length ≤ B+2 :=
      (cacheWord_length prior old).trans (by omega)
    have hxs : ∀ x ∈ xs, x.length ≤ B+2 := by
      intro x h
      have hh := hx x (by simp [h])
      omega
    obtain ⟨r₁,hg₁,hp₁⟩ := parse_cons regs acc (prior,[]) (old,[])
      (xs.map fun x => (x,[]))
    obtain ⟨tc,htc,r₂,hc⟩ := cacheCell_eval r₁ acc prior old
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨r₃,he⟩ := cacheEmit_eval r₂ acc (cacheWord prior old)
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨tt,htt,r₄,hg₄,ht⟩ := ih r₃
      ((LayoutScalarEmitter.record (cacheWord prior old) []).reverse++acc.1,acc.2)
      (cacheWord prior old) (B+2) hn hxs
    cases ht with
    | seq hparse hwhile =>
      rename_i tp tw between
      refine ⟨6*pairLength (old,[])+11+(tc+(18*(cacheWord prior old).length+39)+tp+tw+1),
        ?_,r₄,hg₄,?_⟩
      · simp only [pairLength,List.length_nil,Nat.add_zero,List.length_cons] at *
        have hm : max prior.length old.length ≤ B := by omega
        have hwork :
            6 * old.length + 11 + (tc + (18 * (cacheWord prior old).length + 39)) + 1 ≤
              200 * (B + 2 * xs.length + 6) := by
          omega
        have htt' : tp + tw ≤
            200 * (xs.length + 1) * (B + 2 * xs.length + 6) := by
          have hinner : B + 2 + 2 * xs.length + 4 =
              B + (2 * xs.length + 6) := by omega
          rw [hinner] at htt
          exact htt
        calc
          6 * old.length + 11 +
                (tc + (18 * (cacheWord prior old).length + 39) + tp + tw + 1) =
              (6 * old.length + 11 + (tc + (18 * (cacheWord prior old).length + 39)) + 1) +
                (tp + tw) := by omega
          _ ≤ 200 * (B + 2 * xs.length + 6) +
                200 * (xs.length + 1) * (B + 2 * xs.length + 6) :=
            Nat.add_le_add hwork htt'
          _ = 200 * ((old :: xs).length + 1) *
                (B + 2 * (old :: xs).length + 4) := by
            simp only [List.length_cons]
            ring
      · have hall := hp₁.seq (.while_true hg₁ (hc.seq (he.seq hparse)) hwhile)
        simpa [cacheRow,cacheScan,cacheLast,cacheRecords,List.reverse_append,
          List.append_assoc,Nat.add_assoc] using hall

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheFinishPorts : Fin 7 → Fin 18 := ![0,1,16,5,6,7,15]
theorem cacheFinishPorts_injective : Function.Injective cacheFinishPorts := by decide

abbrev cacheFinishList : Cmd 8 18 :=
  liftCommand LayoutScalarEmitter.finishList 2 6 id cacheFinishPorts

theorem cacheFinishList_eval (regs : Fin 8 → Bool) (acc : WordPair) (prior : List Bool) :
    ∃ r, Eval cacheFinishList (3*acc.1.length+9)
      (state regs acc (prior,[]) ([],[]) [])
      (state r ([],acc.2) (prior,[]) ([],[]) (acc.1.reverse++[false])) := by
  let d := state regs acc (prior,[]) ([],[]) []
  let a := projectState id cacheFinishPorts d
  obtain ⟨e,he,hs⟩ := LayoutScalarEmitter.finishList_eval a
    (by simp [a,d,projectState,cacheFinishPorts,state])
  have h := eval_liftCommand_from_state LayoutScalarEmitter.finishList 2 6
    id cacheFinishPorts d Function.injective_id cacheFinishPorts_injective he
  have hout : embedState id cacheFinishPorts d e =
      state e.regs ([],acc.2) (prior,[]) ([],[]) (acc.1.reverse++[false]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      exact embedState_register id cacheFinishPorts d e Function.injective_id i
    · rw [hs,ProgramLinking.extend_update cacheFinishPorts_injective,
        ProgramLinking.extend_update cacheFinishPorts_injective]
      have hbase := congrArg StructuredProgram.State.stacks
        (embedState_project id cacheFinishPorts d Function.injective_id cacheFinishPorts_injective)
      change Function.extend cacheFinishPorts a.stacks d.stacks = d.stacks at hbase
      rw [hbase]
      funext j
      fin_cases j <;> simp [a,d,projectState,cacheFinishPorts,state]
  refine ⟨e.regs,?_⟩
  rw [hout] at h
  simpa [cacheFinishList,a,d,projectState,cacheFinishPorts,state,Nat.add_assoc] using h

abbrev cacheClear : Cmd 8 18 := .call (StackRoutines.clearProgram 0 0 1)

theorem cacheClear_eval (regs : Fin 8 → Bool) (acc : WordPair) (prior queue : List Bool) :
    Eval cacheClear (2*prior.length+3)
      (state regs acc (prior,[]) ([],[]) queue)
      (state (readRegs regs 0 1 none) acc ([],[]) ([],[]) queue) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (0 : Fin 18) (0 : Fin 8) 1
    (state regs acc (prior,[]) ([],[]) queue)
  have hs : StackRoutines.clearStacks 0 (state regs acc (prior,[]) ([],[]) queue).stacks =
      (state (readRegs regs 0 1 none) acc ([],[]) ([],[]) queue).stacks := by
    funext j
    fin_cases j <;> simp [state,StackRoutines.clearStacks]
  rw [hs] at h
  have h0 : (state regs acc (prior, []) ([], []) queue).stacks 0 = prior := by
    simp [state]
  have hr : (state regs acc (prior, []) ([], []) queue).regs = regs := rfl
  rw [h0, hr] at h
  simpa only [cacheClear, state] using h

abbrev cachePass : Cmd 8 18 := .seq cacheRow (.seq cacheFinishList cacheClear)

theorem cacheLast_length (prior : List Bool) (xs : List (List Bool))
    (B : ℕ) (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    (cacheLast prior xs).length ≤ B+2*xs.length := by
  induction xs generalizing prior B with
  | nil => simpa [cacheLast] using hp
  | cons old xs ih =>
    have ho := hx old (by simp)
    have hn : (cacheWord prior old).length ≤ B+2 :=
      (cacheWord_length prior old).trans (by omega)
    have ht := ih (cacheWord prior old) (B+2) hn (by
      intro x h
      have hh := hx x (by simp [h]); omega)
    simpa [cacheLast,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem cacheRecords_length_le (xs : List (List Bool)) (B : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ B) :
    (cacheRecords xs).length ≤ xs.length*(2*B+3) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := hx x (by simp)
    have ht := ih (by intro y h; exact hx y (by simp [h]))
    simp only [cacheRecords_cons,List.length_append,LayoutScalarEmitter.record_length,
      List.length_nil,Nat.add_zero,List.length_cons]
    nlinarith

theorem cachePass_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (counter : List Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 300*(xs.length+1)*(B+2*xs.length+4), ∃ r,
      Eval cachePass t
        (state regs ([],counter) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
        (state r ([],counter) ([],[]) ([],[])
          (pairEncoding ((cacheScan [] xs).map fun x => (x,[])))) := by
  obtain ⟨tr,htr,r₁,_,hr⟩ := cacheRow_eval xs regs ([],counter) [] B (by simp) hx
  obtain ⟨r₂,hf⟩ := cacheFinishList_eval r₁
    ((cacheRecords (cacheScan [] xs)).reverse++[],counter) (cacheLast [] xs)
  have hc := cacheClear_eval r₂ ([],counter) (cacheLast [] xs)
    (((cacheRecords (cacheScan [] xs)).reverse++[]).reverse++[false])
  have hout : ((cacheRecords (cacheScan [] xs)).reverse++[]).reverse++[false] =
      pairEncoding ((cacheScan [] xs).map fun x => (x,[])) := by
    simpa using (cacheRecords_encoding (cacheScan [] xs)).symm
  have hword := cacheScan_word_length [] xs B (by simp) hx
  have hlen := cacheRecords_length_le (cacheScan [] xs) (B+2*xs.length) hword
  rw [cacheScan_length] at hlen
  have hlast := cacheLast_length [] xs B (by simp) hx
  refine ⟨tr+((3*((cacheRecords (cacheScan [] xs)).reverse++[]).length+9)+
      (2*(cacheLast [] xs).length+3)),?_,readRegs r₂ 0 1 none,?_⟩
  · simp only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero]
    let inner := B + 2 * xs.length + 4
    have hinner : 1 ≤ inner := by dsimp [inner]; omega
    have hrec : (cacheRecords (cacheScan [] xs)).length ≤
        2 * xs.length * inner := by
      calc
        (cacheRecords (cacheScan [] xs)).length ≤
            xs.length * (2 * (B + 2 * xs.length) + 3) := hlen
        _ ≤ xs.length * (2 * inner) := by
          apply Nat.mul_le_mul_left
          dsimp [inner]
          omega
        _ = 2 * xs.length * inner := by ring
    have hlast' : (cacheLast [] xs).length ≤ inner := by
      exact hlast.trans (by dsimp [inner]; omega)
    have hrec3 := Nat.mul_le_mul_left 3 hrec
    have hlast2 := Nat.mul_le_mul_left 2 hlast'
    have hconst : 12 ≤ 12 * inner := by omega
    have hover : 3 * (cacheRecords (cacheScan [] xs)).length + 9 +
        (2 * (cacheLast [] xs).length + 3) ≤
          100 * (xs.length + 1) * inner := by
      calc
        3 * (cacheRecords (cacheScan [] xs)).length + 9 +
              (2 * (cacheLast [] xs).length + 3) =
            (3 * (cacheRecords (cacheScan [] xs)).length +
              2 * (cacheLast [] xs).length) + 12 := by omega
        _ ≤ (3 * (2 * xs.length * inner) + 2 * inner) + 12 :=
          Nat.add_le_add_right (Nat.add_le_add hrec3 hlast2) 12
        _ = 6 * xs.length * inner + 2 * inner + 12 := by ring
        _ ≤ 6 * xs.length * inner + 2 * inner + 12 * inner := by omega
        _ = (6 * xs.length + 14) * inner := by ring
        _ ≤ (100 * (xs.length + 1)) * inner :=
          Nat.mul_le_mul_right inner (by omega)
        _ = 100 * (xs.length + 1) * inner := by ring
    calc
      tr + (3 * (cacheRecords (cacheScan [] xs)).length + 9 +
          (2 * (cacheLast [] xs).length + 3)) ≤
        200 * (xs.length + 1) * inner + 100 * (xs.length + 1) * inner :=
          Nat.add_le_add htr hover
      _ = 300 * (xs.length + 1) * (B + 2 * xs.length + 4) := by
        dsimp [inner]
        ring
  · simpa only [hout] using hr.seq (hf.seq hc)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheIter : ℕ → List (List Bool) → List (List Bool)
  | 0, xs => xs
  | n+1, xs => cacheIter n (cacheScan [] xs)

@[simp] theorem cacheIter_length (n : ℕ) (xs : List (List Bool)) :
    (cacheIter n xs).length = xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [cacheIter,ih]

theorem cacheIter_word_length (n : ℕ) (xs : List (List Bool)) (B : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ cacheIter n xs, x.length ≤ B+2*n*xs.length := by
  induction n generalizing xs B with
  | zero => simpa [cacheIter] using hx
  | succ n ih =>
    have hs := cacheScan_word_length [] xs B (by simp) hx
    have ht := ih (cacheScan [] xs) (B+2*xs.length) hs
    simpa [cacheIter,Nat.mul_add,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

abbrev cacheRead : Cmd 8 18 := .base (.atom (.pop 17 7 6))

def cacheAfterRead (regs : Fin 8 → Bool) (counter : List Bool)
    (xs : List (List Bool)) : Data :=
  state (readRegs regs 7 6 counter.head?) ([],counter.tail) ([],[]) ([],[])
    (pairEncoding (xs.map fun x => (x,[])))

theorem cacheRead_eval (regs : Fin 8 → Bool) (counter : List Bool)
    (xs : List (List Bool)) :
    Eval cacheRead 1
      (state regs ([],counter) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
      (cacheAfterRead regs counter xs) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (17 : Fin 18) (7 : Fin 8) 6)
    (state regs ([],counter) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[])))))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;>
      simp [state,StructuredProgram.Atom.instr,execInstr]

abbrev cacheLoop : Cmd 8 18 := .while 6 (.seq cachePass cacheRead)

theorem cacheLoop_eval (counter : List Bool) (xs : List (List Bool))
    (regs : Fin 8 → Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 400*(counter.length+1)*(xs.length+1)*(B+2*counter.length*xs.length+4),
    ∃ r, Eval cacheLoop t (cacheAfterRead regs counter xs)
      (state r ([],[]) ([],[]) ([],[])
        (pairEncoding ((cacheIter counter.length xs).map fun x => (x,[])))) := by
  induction counter generalizing xs regs B with
  | nil =>
    refine ⟨1,by simp; nlinarith,readRegs regs 7 6 none,?_⟩
    simpa [cacheLoop,cacheAfterRead,cacheIter] using
      (Eval.while_false (test := (6 : Fin 8)) (body := .seq cachePass cacheRead)
        (a := cacheAfterRead regs [] xs)
        (by simp [cacheAfterRead,state,readRegs_present]))
  | cons bit counter ih =>
    let rr := readRegs regs 7 6 (some bit)
    obtain ⟨tp,htp,rp,hp⟩ := cachePass_eval xs rr counter B hx
    have hr := cacheRead_eval rp counter (cacheScan [] xs)
    have hscan := cacheScan_word_length [] xs B (by simp) hx
    obtain ⟨tl,htl,rl,hl⟩ := ih (cacheScan [] xs) rp (B+2*xs.length) hscan
    refine ⟨tp+1+tl+1,?_,rl,?_⟩
    · rw [cacheScan_length] at htl
      simp only [List.length_cons]
      have henv : B+2*xs.length+2*counter.length*xs.length+4 =
          B+2*(counter.length+1)*xs.length+4 := by ring
      rw [henv] at htl
      have he : B+2*xs.length+4 ≤ B+2*(counter.length+1)*xs.length+4 := by nlinarith
      have hprod := Nat.mul_le_mul_left (300*(xs.length+1)) he
      nlinarith
    · have he := Eval.while_true (test := (6 : Fin 8))
        (by simp [state,rr,readRegs_present]) (hp.seq hr) hl
      simpa [cacheLoop,cacheAfterRead,cacheIter,rr] using he

abbrev cacheCommand : Cmd 8 18 := .seq cacheRead cacheLoop
def cacheProgram := compiled cacheCommand 17 15

theorem cacheProgram_runsIn (counter : List Bool) (xs : List (List Bool))
    (regs : Fin 8 → Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ r, RunsIn cacheProgram
      (400*(counter.length+1)*(xs.length+1)*(B+2*counter.length*xs.length+4)+2)
      ((state regs ([],counter) ([],[]) ([],[])
        (pairEncoding (xs.map fun x => (x,[])))).withPC (some cacheProgram.entry))
      ((state r ([],[]) ([],[]) ([],[])
        (pairEncoding ((cacheIter counter.length xs).map fun x => (x,[])))).withPC none) := by
  obtain ⟨t,ht,r,he⟩ := cacheLoop_eval counter xs regs B hx
  refine ⟨r,1+t+1,by omega,?_⟩
  exact compiled_halt_trace ((cacheRead_eval regs counter xs).seq he) 17 15

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

theorem cacheScan_values (prior : List Bool) (xs : List (List Bool)) :
    (cacheScan prior xs).map BinaryArithmetic.toNat = scanDouble (BinaryArithmetic.toNat prior) (xs.map BinaryArithmetic.toNat) := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp only [cacheScan,List.map_cons,scanDouble,ih,cacheWord_value]

theorem cacheIter_values (n A R : ℕ) (xs : List (List Bool))
    (hx : xs.map BinaryArithmetic.toNat = (List.range R).map (H A)) :
    (cacheIter n xs).map BinaryArithmetic.toNat = (List.range R).map (H (A+n)) := by
  induction n generalizing A xs with
  | zero => simpa [cacheIter] using hx
  | succ n ih =>
    have hs : (cacheScan [] xs).map BinaryArithmetic.toNat = (List.range R).map (H (A+1)) := by
      rw [cacheScan_values,hx]
      exact scanDouble_H A R
    simpa [cacheIter,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (A+1) _ hs

def initialCache (R : ℕ) : List (List Bool) := List.replicate R [true]

@[simp] theorem initialCache_length (R : ℕ) : (initialCache R).length = R := by
  simp [initialCache]

theorem initialCache_values (R : ℕ) :
    (initialCache R).map BinaryArithmetic.toNat = (List.range R).map (H 0) := by
  have hh : H 0 = fun _ : ℕ => 1 := funext H_zero
  simp [initialCache,hh,BinaryArithmetic.toNat,bitVal]

theorem cacheIter_initial_values (A R : ℕ) :
    (cacheIter A (initialCache R)).map BinaryArithmetic.toNat = (List.range R).map (H A) := by
  simpa using cacheIter_values A 0 R (initialCache R) (initialCache_values R)

theorem cacheIter_initial_word_length (A R : ℕ) :
    ∀ x ∈ cacheIter A (initialCache R), x.length ≤ 1+2*A*R := by
  have h := cacheIter_word_length A (initialCache R) 1 (by
    intro x hx
    simp only [initialCache,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    rfl)
  simpa using h

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

private def initialPorts : UnaryForPrograms.Ports 8 18 := ⟨17,7,6⟩

def initialRecord : List Bool := [true,true,true,false,false]

abbrev initialBody : Cmd 8 18 := ArithmeticExpressionSupport.pushWord 15 initialRecord

abbrev initialCommand : Cmd 8 18 :=
  .seq (ArithmeticExpressionSupport.pushWord 15 [false])
    (UnaryForPrograms.forCmd initialPorts initialBody)

theorem initialRecord_encoding (xs : List WordPair) :
    initialRecord ++ pairEncoding xs = pairEncoding (([true],[])::xs) := rfl

private def InitialInvariant (base : Data) (i : ℕ) (d : Data) : Prop :=
  d.stacks 15 = pairEncoding (List.replicate i ([true],[])) ∧
  ∀ j, j ≠ 15 → j ≠ 17 → d.stacks j = base.stacks j

private theorem initial_stable (base : Data) :
    UnaryForPrograms.FrameStable initialPorts (InitialInvariant base) := by
  intro i a b hab hi
  refine ⟨?_,fun j hj hk => (hab j hk).symm.trans (hi.2 j hj hk)⟩
  exact (hab 15 (by decide)).symm.trans hi.1

private theorem initial_body (base : Data) :
    UnaryForPrograms.BodySpec initialPorts initialBody (InitialInvariant base) (fun _ => 10) := by
  intro i d hi
  obtain ⟨r,he⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) initialRecord d
  refine ⟨10,⟨r,Function.update d.stacks 15 (initialRecord++d.stacks 15)⟩,le_rfl,he,by simp [initialPorts],?_,?_⟩
  · simp only [Function.update_same, hi.1, initialRecord_encoding, List.replicate_succ]
  · intro j hj hk
    simpa [hj] using hi.2 j hj hk

theorem initialCommand_eval (regs : Fin 8 → Bool) (counter : List Bool) :
    ∃ t ≤ 12*counter.length+4, ∃ r,
      Eval initialCommand t (state regs ([],counter) ([],[]) ([],[]) [])
        (state r ([],[]) ([],[]) ([],[])
          (pairEncoding (List.replicate counter.length ([true],[])))) := by
  let d := state regs ([],counter) ([],[]) ([],[]) []
  obtain ⟨r₀,h₀⟩ := ArithmeticExpressionSupport.pushWord_eval (15 : Fin 18) [false] d
  let a : Data := ⟨r₀,Function.update d.stacks 15 [false]⟩
  have hi : InitialInvariant d 0 a := by
    constructor
    · rfl
    · intro j hj _; simp [a,hj]
  obtain ⟨t,e,he,hi',hc,ht⟩ := UnaryForPrograms.for_correct initialPorts initialBody
    (InitialInvariant d) (fun _ => 10) (initial_stable d) (initial_body d) a hi
  have hc' : e.stacks 17 = [] := hc
  have hi'₁ : e.stacks 15 = pairEncoding (List.replicate counter.length ([true],[])) := by
    simpa [a,d,state,initialPorts] using hi'.1
  have heq : e = state e.regs ([],[]) ([],[]) ([],[])
      (pairEncoding (List.replicate counter.length ([true],[]))) := by
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
  · have hb : CounterForPrograms.budgetSum (fun _ => 10) 0 counter.length = 10*counter.length := by
      rw [CounterForPrograms.budgetSum_const, Nat.mul_comm]
    have ht' : t ≤ 10*counter.length+2*counter.length+2 := by
      simpa [a,d,state,initialPorts,hb] using ht
    omega
  · have hh : Eval initialCommand (2+t) d e := h₀.seq he
    rw [heq] at hh
    exact hh

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

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
  .call (ProgramLinking.liftProgram cacheProgram id cacheBuildPorts)

theorem initialBuild_eval (regs : Fin 8 → Bool) (a r : List Bool) :
    ∃ t ≤ 12*r.length+5, ∃ regs',
      Eval initialBuild t (buildState regs a r [])
        (buildState regs' a [] (pairEncoding (List.replicate r.length ([true],[])))) := by
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
        (pairEncoding (List.replicate r.length ([true],[])))) =
      buildState regs' a [] (pairEncoding (List.replicate r.length ([true],[]))) := by
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
    ∃ t ≤ 400*(a.length+1)*(xs.length+1)*(B+2*a.length*xs.length+4)+2,
    ∃ regs', Eval cacheBuildLoop t
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (buildState regs' [] [] (pairEncoding ((cacheIter a.length xs).map fun x => (x,[])))) := by
  obtain ⟨regs',t,ht,he⟩ := cacheProgram_runsIn a xs regs B hx
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
        (pairEncoding ((cacheIter a.length xs).map fun x => (x,[])))) =
      buildState regs' [] [] (pairEncoding ((cacheIter a.length xs).map fun x => (x,[]))) := by
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
  have h := eval_call_lifted cacheProgram id cacheBuildPorts
    (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
    Function.injective_id cacheBuildPorts_injective he
  rw [hs,hf] at h
  exact ⟨t,ht,regs',h⟩

abbrev buildCommand : Cmd 8 19 := .seq initialBuild cacheBuildLoop
def buildProgram := compiled buildCommand 17 15

theorem buildProgram_runsIn (regs : Fin 8 → Bool) (a r : List Bool) :
    ∃ (regs' : Fin 8 → Bool) (xs : List (List Bool)),
      RunsIn buildProgram
        (12*r.length+400*(a.length+1)*(r.length+1)*(2*a.length*r.length+5)+8)
        ((buildState regs a r []).withPC (some buildProgram.entry))
        ((buildState regs' [] [] (pairEncoding (xs.map fun x => (x,[])))).withPC none) ∧
      xs.length = r.length ∧
      xs.map BinaryArithmetic.toNat = (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) ∧
      (∀ x ∈ xs, x.length ≤ 1+2*a.length*r.length) := by
  obtain ⟨ti,hti,ri,hi⟩ := initialBuild_eval regs a r
  have hw : ∀ x ∈ initialCache r.length, x.length ≤ 1 := by
    intro x hx
    simp only [initialCache,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    rfl
  obtain ⟨tc,htc,rc,hc⟩ := cacheBuildLoop_eval ri a (initialCache r.length) 1 hw
  have hh : (initialCache r.length).map (fun x => (x,([] : List Bool))) =
      List.replicate r.length ([true],[]) := by simp [initialCache]
  rw [hh] at hc
  refine ⟨rc,cacheIter a.length (initialCache r.length),
    ⟨ti+tc+1,?_,compiled_halt_trace (hi.seq hc) 17 15⟩,?_,?_,?_⟩
  · simp only [initialCache_length] at htc
    have hnorm : 1+2*a.length*r.length+4 = 2*a.length*r.length+5 := by omega
    rw [hnorm] at htc
    omega
  · simp
  · exact cacheIter_initial_values a.length r.length
  · exact cacheIter_initial_word_length a.length r.length

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
