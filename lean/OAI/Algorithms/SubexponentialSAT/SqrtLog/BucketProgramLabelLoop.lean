import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramLabel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramGrouping

namespace OAI.Algorithms

/-! A fixed controller labels an explicit runtime list of head assignments.
The only enumeration intended here is the 2^h head list. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Label
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def peek : Code := .base (.atom (.peek 15 0 1))
def body : Code := .seq step peek
def loop : Code := .while 0 body
def command : Code := .seq peek loop
def program := compiled command 15 19

def ready (regs : Fin 8 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (pending : List (List Bool)) (records keys : List Bool) : Data :=
  state (readRegs regs 0 1 (ProgramEncoding.encodeRecords pending).head?) W rows js n pending records keys

def recordOutput (W : List Bool) (rows : List (List (List Bool))) (js : List ℕ) (n : ℕ) :
    List (List Bool) → List Bool → List Bool
  | [], acc => acc
  | bits::rest, acc => recordOutput W rows js n rest
      (Encoding.frame (key W bits rows)++Encoding.frame (HeadScatterProgram.mask n js bits)++acc)

def keyOutput (W : List Bool) (rows : List (List (List Bool))) :
    List (List Bool) → List Bool → List Bool
  | [], acc => acc
  | bits::rest, acc => keyOutput W rows rest (true::(Encoding.frame (key W bits rows)++acc))

def cost (W : List Bool) (rows : List (List (List Bool))) (js : List ℕ) (n : ℕ)
    (pending : List (List Bool)) : ℕ :=
  (pending.map (fun bits => stepCost W bits rows js n+2)).sum+1

theorem peek_eval (regs : Fin 8 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (pending : List (List Bool)) (records keys : List Bool) :
    Eval peek 1 (state regs W rows js n pending records keys)
      (ready regs W rows js n pending records keys) := Eval.base (StructuredProgram.Eval.atom _ _)

theorem loop_eval (regs : Fin 8 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (pending : List (List Bool)) (records keys : List Bool)
    (hrows : ∀ bits∈pending, ∀ row∈rows,row.length=bits.length)
    (hlen : ∀ bits∈pending,js.length=bits.length) (hjs : ∀ j∈js,j < n) :
    ∃ t ≤ cost W rows js n pending, ∃ rf,
      Eval loop t (ready regs W rows js n pending records keys)
        (state rf W rows js n [] (recordOutput W rows js n pending records)
          (keyOutput W rows pending keys)) := by
  induction pending generalizing regs records keys with
  | nil =>
      refine ⟨1,by simp [cost],(ready regs W rows js n [] records keys).regs,?_⟩
      exact Eval.while_false (by
        simp [ready,state,ProgramEncoding.encodeRecords,Encoding.encodeList,readRegs])
  | cons bits rest ih =>
      obtain ⟨t,ht,rm,he⟩ := step_eval (ready regs W rows js n (bits::rest) records keys).regs
        W bits rows js n rest records keys (hrows bits (by simp)) (hlen bits (by simp)) hjs
      obtain ⟨u,hu,rf,hf⟩ := ih rm
        (Encoding.frame (key W bits rows)++Encoding.frame (HeadScatterProgram.mask n js bits)++records)
        (true::(Encoding.frame (key W bits rows)++keys))
        (by intro b hb; exact hrows b (by simp [hb]))
        (by intro b hb; exact hlen b (by simp [hb]))
      have hg : (ready regs W rows js n (bits::rest) records keys).regs 0=true := by
        simp [ready,state,ProgramEncoding.encodeRecords,Encoding.encodeList,readRegs]
      have hr := Eval.while_true hg (he.seq (peek_eval rm W rows js n rest _ _)) hf
      refine ⟨(t+1)+u+1,?_,rf,hr⟩
      simp only [cost,List.map_cons,List.sum_cons] at *
      omega

theorem command_eval (regs : Fin 8 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (pending : List (List Bool)) (records keys : List Bool)
    (hrows : ∀ bits∈pending, ∀ row∈rows,row.length=bits.length)
    (hlen : ∀ bits∈pending,js.length=bits.length) (hjs : ∀ j∈js,j < n) :
    ∃ t ≤ cost W rows js n pending+1, ∃ rf,
      Eval command t (state regs W rows js n pending records keys)
        (state rf W rows js n [] (recordOutput W rows js n pending records)
          (keyOutput W rows pending keys)) := by
  obtain ⟨t,ht,rf,he⟩ := loop_eval regs W rows js n pending records keys hrows hlen hjs
  exact ⟨1+t,by omega,rf,(peek_eval regs W rows js n pending records keys).seq he⟩

theorem program_runsIn (regs : Fin 8 → Bool) (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n : ℕ) (pending : List (List Bool)) (records keys : List Bool)
    (hrows : ∀ bits∈pending, ∀ row∈rows,row.length=bits.length)
    (hlen : ∀ bits∈pending,js.length=bits.length) (hjs : ∀ j∈js,j < n) :
    ∃ rf, RunsIn program (cost W rows js n pending+2)
      ((state regs W rows js n pending records keys).withPC (some program.entry))
      ((state rf W rows js n [] (recordOutput W rows js n pending records)
        (keyOutput W rows pending keys)).withPC none) := by
  obtain ⟨t,ht,rf,he⟩ := command_eval regs W rows js n pending records keys hrows hlen hjs
  exact ⟨rf,⟨t+1,by omega,compiled_halt_trace he 15 19⟩⟩

def labelled (W : List Bool) (rows : List (List (List Bool))) (js : List ℕ) (n : ℕ)
    (pending : List (List Bool)) : List SubexponentialSAT.Subexp.BucketProgram.Record :=
  pending.map (fun bits => (key W bits rows,HeadScatterProgram.mask n js bits))

theorem encoded_records_append (xs ys : List SubexponentialSAT.Subexp.BucketProgram.Record) :
    SubexponentialSAT.Subexp.BucketProgram.encodeRecords (xs++ys) =
      SubexponentialSAT.Subexp.BucketProgram.encodeRecords xs++SubexponentialSAT.Subexp.BucketProgram.encodeRecords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [SubexponentialSAT.Subexp.BucketProgram.encodeRecords,ih,List.append_assoc]

theorem recordOutput_eq (W : List Bool) (rows : List (List (List Bool))) (js : List ℕ) (n : ℕ)
    (pending : List (List Bool)) (acc : List Bool) :
    recordOutput W rows js n pending acc =
      SubexponentialSAT.Subexp.BucketProgram.encodeRecords (labelled W rows js n pending).reverse++acc := by
  induction pending generalizing acc with
  | nil => rfl
  | cons bits rest ih =>
      rw [recordOutput,ih]
      simp [labelled,List.reverse_cons,encoded_records_append,
        SubexponentialSAT.Subexp.BucketProgram.encodeRecords,List.append_assoc]

theorem keyOutput_eq (W : List Bool) (rows : List (List (List Bool)))
    (pending acc : List (List Bool)) :
    keyOutput W rows pending (ProgramEncoding.encodeRecords acc) =
      ProgramEncoding.encodeRecords ((pending.map (fun bits => key W bits rows)).reverse++acc) := by
  induction pending generalizing acc with
  | nil => rfl
  | cons bits rest ih =>
      change keyOutput W rows rest (ProgramEncoding.encodeRecords (key W bits rows::acc)) = _
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

end SubexponentialSAT.SqrtLog.BucketProgram.Label

end OAI.Algorithms
