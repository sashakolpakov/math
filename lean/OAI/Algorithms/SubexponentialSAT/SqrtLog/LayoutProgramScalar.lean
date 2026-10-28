import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramStream
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithmEntry

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev Data := State 8 18

def state (regs : Fin 8 → Bool) (acc work next : WordPair)
    (queue : List Bool) : Data :=
  ⟨regs, fun j => if j=0 then work.1 else if j=1 then work.2 else
    if j=2 then next.1 else if j=3 then next.2 else if j=15 then queue else
    if j=16 then acc.1 else if j=17 then acc.2 else []⟩

def workPorts : Fin 16 → Fin 18 := Fin.castAdd 2

theorem workPorts_injective : Function.Injective workPorts := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 18 => k.val) h

abbrev workCall (c : Cmd 8 16) : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram (compiled c 0 1) id workPorts)

theorem workCall_eval {c : Cmd 8 16} {t : ℕ}
    {regs regs' : Fin 8 → Bool} {work next work' next' : WordPair}
    {queue queue' : List Bool}
    (he : Eval c t (streamData regs work next queue)
      (streamData regs' work' next' queue')) (acc : WordPair) :
    Eval (workCall c) (t+1) (state regs acc work next queue)
      (state regs' acc work' next' queue') := by
  have emb (r : Fin 8 → Bool) (w n : WordPair) (q : List Bool) :
      embedState id workPorts (state regs acc work next queue)
        (streamData r w n q) = state r acc w n q := by
    apply embedState_eq_of_ports id workPorts _ _ _
      Function.injective_id workPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [state, streamData, workPorts]
    · intro i hi
      have hv : 16 ≤ i.val := by
        by_contra h
        have hlt : i.val < 16 := by omega
        exact hi ⟨⟨i.val,hlt⟩, Fin.ext rfl⟩
      fin_cases i <;> simp_all [state]
  have h := eval_call_lifted (compiled c 0 1) id workPorts
    (state regs acc work next queue) Function.injective_id workPorts_injective
    (compiled_halt_trace he 0 1)
  simpa only [workCall, emb] using h

abbrev parse : Cmd 8 18 := workCall parsePair
abbrev multiply : Cmd 8 18 := workCall (streamOperation true)

theorem parse_cons (regs : Fin 8 → Bool) (acc work next : WordPair)
    (rest : List WordPair) :
    ∃ r, r 7 = true ∧ Eval parse (6*pairLength next+11)
      (state regs acc work ([],[]) (pairEncoding (next::rest)))
      (state r acc work next (pairEncoding rest)) := by
  obtain ⟨r,hg,he⟩ := parsePair_cons regs work next rest
  exact ⟨r,hg,by simpa only [parse, Nat.add_assoc] using workCall_eval he acc⟩

theorem parse_nil (regs : Fin 8 → Bool) (acc work : WordPair) :
    ∃ r, r 7 = false ∧ Eval parse 3
      (state regs acc work ([],[]) (pairEncoding []))
      (state r acc work ([],[]) []) := by
  obtain ⟨r,hg,he⟩ := parsePair_nil regs work
  exact ⟨r,hg,workCall_eval he acc⟩

theorem multiply_eval (regs : Fin 8 → Bool) (acc work next : WordPair)
    (queue : List Bool) :
    ∃ t ≤ 25000*(pairLength work+pairLength next+3)^2+2,
    ∃ r result, Eval multiply t (state regs acc work next queue)
      (state r acc result ([],[]) queue) ∧
      pairValue result = pairValue work * pairValue next ∧
      pairLength result ≤ 2*(pairLength work+pairLength next)+6 := by
  obtain ⟨t,ht,r,result,he,hv,hl⟩ := streamOperation_eval true regs work next queue
  exact ⟨t+1,by omega,r,result,workCall_eval he acc,
    by simpa only [combine,↓reduceIte] using hv,
    by simpa only [wordGrowth,↓reduceIte] using hl⟩

def sumPorts : Fin 16 → Fin 18 :=
  ![16,17,0,1,2,3,4,5,6,7,8,9,10,11,12,15]

theorem sumPorts_injective : Function.Injective sumPorts := by decide

abbrev accumulate : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram (compiled (streamOperation false) 0 1) id sumPorts)

theorem accumulate_eval (regs : Fin 8 → Bool) (acc work : WordPair)
    (queue : List Bool) :
    ∃ t ≤ 25000*(pairLength acc+pairLength work+3)^2+2,
    ∃ r result, Eval accumulate t (state regs acc work ([],[]) queue)
      (state r result ([],[]) ([],[]) queue) ∧
      pairValue result = pairValue acc + pairValue work ∧
      pairLength result ≤ pairLength acc+pairLength work+2 := by
  obtain ⟨t,ht,r,result,he,hv,hl⟩ := streamOperation_eval false regs acc work queue
  have hs : embedState id sumPorts (state regs acc work ([],[]) queue)
      (streamData regs acc work queue) = state regs acc work ([],[]) queue := by
    apply embedState_eq_of_ports id sumPorts _ _ _ Function.injective_id sumPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [state,streamData,sumPorts]
    · intro i hi; rfl
  have hf : embedState id sumPorts (state regs acc work ([],[]) queue)
      (streamData r result ([],[]) queue) = state r result ([],[]) ([],[]) queue := by
    apply embedState_eq_of_ports id sumPorts _ _ _ Function.injective_id sumPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [state,streamData,sumPorts]
    · intro i hi
      have h16 : i ≠ 16 := fun h => hi ⟨0, by simpa [sumPorts] using h.symm⟩
      have h17 : i ≠ 17 := fun h => hi ⟨1, by simpa [sumPorts] using h.symm⟩
      have h0 : i ≠ 0 := fun h => hi ⟨2, by simpa [sumPorts] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨3, by simpa [sumPorts] using h.symm⟩
      simp [state,h16,h17,h0,h1]
  have hc := eval_call_lifted (compiled (streamOperation false) 0 1) id sumPorts
    (state regs acc work ([],[]) queue) Function.injective_id sumPorts_injective
    (compiled_halt_trace he 0 1)
  rw [hs,hf] at hc
  exact ⟨t+1,by omega,r,result,hc,
    by simpa only [combine,Bool.false_eq_true,↓reduceIte] using hv,
    by simpa only [wordGrowth,Bool.false_eq_true,↓reduceIte] using hl⟩

def one : WordPair := ([true],[])

@[simp] theorem one_length : pairLength one = 1 := rfl
@[simp] theorem one_value : pairValue one = 1 := rfl

abbrev initializeOne : Cmd 8 18 :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 0 0)))

theorem initializeOne_eval (regs : Fin 8 → Bool) (acc next : WordPair)
    (queue : List Bool) :
    Eval initializeOne 2 (state regs acc ([],[]) next queue)
      (state (Function.update regs 0 true) acc one next queue) := by
  let r := Function.update regs 0 true
  have hs : Eval (.base (.atom (.set 0 true))) 1
      (state regs acc ([],[]) next queue) (state r acc ([],[]) next queue) :=
    .base (.atom _ _)
  have hp : Eval (.base (.atom (.push 0 0))) 1
      (state r acc ([],[]) next queue) (state r acc one next queue) := by
    convert (Eval.base (SubexponentialSAT.StructuredProgram.Eval.atom
      (.push (0 : Fin 18) (0 : Fin 8)) (state r acc ([],[]) next queue))) using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [state,one,r,StructuredProgram.Atom.instr,execInstr]
  exact hs.seq hp

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
