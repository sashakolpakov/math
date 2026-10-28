import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryTally
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A fixed bit zipper counts coordinate matches of one-hot words by counting
true bitwise intersections. It consumes one candidate copy and the same number
of table bits, preserving the remaining table suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramAnd
open SubexponentialSAT BitProgram StructuredCalls

def jointTrue (xs ys : List Bool) : ℕ := (List.zipWith (· && ·) xs ys).count true

abbrev program : Program 5 3 11 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 7, .pop 1 2 3 3,
    .branch 0 4 0, .branch 2 5 0, .set 4 false 6, .push 2 4 0,
    .set 2 false 8, .set 3 false 9, .set 4 false 10, .halt]

def stackData (xs ys out : List Bool) : Fin 3 → List Bool := ![xs,ys,out]

def start (regs : Fin 5 → Bool) (xs ys out : List Bool) : Cfg 5 3 11 :=
  ⟨some 0,regs,stackData xs ys out⟩

def finish (ys out : List Bool) : Cfg 5 3 11 :=
  ⟨none,fun _ => false,stackData [] ys out⟩

def nextRegs (regs : Fin 5 → Bool) (a b : Bool) : Fin 5 → Bool :=
  ![a,true,b,true,if a && b then false else regs 4]

def weight (a b : Bool) : ℕ := if a then (if b then 7 else 5) else 4

def steps : List Bool → List Bool → ℕ
  | a::xs,b::ys => weight a b+steps xs ys
  | _,_ => 6

theorem nil_trace (regs : Fin 5 → Bool) (ys out : List Bool) :
    Trace program 6 (start regs [] ys out) (finish ys out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,program,execInstr,start,finish,readRegs,stackData]
  funext i
  fin_cases i <;> simp

theorem cycle (regs : Fin 5 → Bool) (a b : Bool) (xs ys out : List Bool) :
    Trace program (weight a b) (start regs (a::xs) (b::ys) out)
      (start (nextRegs regs a b) xs ys (if a && b then false::out else out)) := by
  cases a <;> cases b <;> apply Computation.Trace.of_iterate <;>
    simp [weight,Function.iterate_succ_apply,step,program,execInstr,start,readRegs,stackData,nextRegs]
  all_goals
    constructor
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp

theorem trace (regs : Fin 5 → Bool) (xs ys tail out : List Bool) (hlen : xs.length=ys.length) :
    Trace program (steps xs ys) (start regs xs (ys++tail) out)
      (finish tail (List.replicate (jointTrue xs ys) false++out)) := by
  induction xs generalizing ys regs out with
  | nil =>
    have hy : ys=[] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simpa [steps,jointTrue] using nil_trace regs tail out
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hh : xs.length=ys.length := by simpa using hlen
      have hc := cycle regs a b xs (ys++tail) out
      have hi := ih (nextRegs regs a b) ys (if a && b then false::out else out) hh
      have h := hc.trans hi
      cases a <;> cases b <;>
        simpa [steps,jointTrue,List.replicate_succ',List.append_assoc,Nat.add_comm] using h

theorem steps_le (xs ys : List Bool) (hlen : xs.length=ys.length) :
    steps xs ys ≤ 7*xs.length+6 := by
  induction xs generalizing ys with
  | nil => simp [steps]
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have h := ih ys (by simpa using hlen)
      have hw : weight a b ≤ 7 := by cases a <;> cases b <;> decide
      simp only [steps,List.length_cons]
      omega

theorem runsIn (regs : Fin 5 → Bool) (xs ys tail out : List Bool) (hlen : xs.length=ys.length) :
    RunsIn program (7*xs.length+6) (start regs xs (ys++tail) out)
      (finish tail (List.replicate (jointTrue xs ys) false++out)) :=
  ⟨steps xs ys,steps_le xs ys hlen,trace regs xs ys tail out hlen⟩

end SubexponentialSAT.SqrtLog.PackingHeadProgramAnd

end OAI.Algorithms
