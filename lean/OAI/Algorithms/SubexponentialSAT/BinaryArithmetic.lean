import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.FixedParameters

namespace OAI.Algorithms

/-!
# Arithmetic on explicit little-endian bit lists

Natural numbers occur in the specification and in theorems about trace lengths.
The data routines inspect Boolean values and list constructors only.
-/

namespace SubexponentialSAT.BinaryArithmetic

def bitVal (b : Bool) : ℕ := if b then 1 else 0

def toNat : List Bool → ℕ
  | [] => 0
  | b :: bs => bitVal b + 2 * toNat bs

@[simp] theorem bitVal_false : bitVal false = 0 := rfl
@[simp] theorem bitVal_true : bitVal true = 1 := rfl
@[simp] theorem toNat_nil : toNat [] = 0 := rfl
@[simp] theorem toNat_cons (b : Bool) (bs : List Bool) :
    toNat (b :: bs) = bitVal b + 2 * toNat bs := rfl

def sumBit (a b c : Bool) : Bool := (a.xor b).xor c
def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem fullAdder_correct (a b c : Bool) :
    bitVal (sumBit a b c) + 2 * bitVal (carryBit a b c) =
      bitVal a + bitVal b + bitVal c := by
  cases a <;> cases b <;> cases c <;> decide

def carryAdd (c : Bool) : List Bool → List Bool
  | [] => if c then [true] else []
  | b :: bs => sumBit false b c :: carryAdd (carryBit false b c) bs

def addCarry (c : Bool) : List Bool → List Bool → List Bool
  | [], ys => carryAdd c ys
  | a :: xs, [] => sumBit a false c :: addCarry (carryBit a false c) xs []
  | a :: xs, b :: ys => sumBit a b c :: addCarry (carryBit a b c) xs ys

def add (xs ys : List Bool) : List Bool := addCarry false xs ys

theorem toNat_carryAdd (c : Bool) (ys : List Bool) :
    toNat (carryAdd c ys) = toNat ys + bitVal c := by
  induction ys generalizing c with
  | nil => cases c <;> simp [carryAdd, bitVal]
  | cons b bs ih =>
      simp only [carryAdd, toNat_cons, ih]
      have h := fullAdder_correct false b c
      simp only [bitVal_false, zero_add] at h
      omega

theorem toNat_addCarry (c : Bool) (xs ys : List Bool) :
    toNat (addCarry c xs ys) = toNat xs + toNat ys + bitVal c := by
  induction xs generalizing c ys with
  | nil => simp [addCarry, toNat_carryAdd]
  | cons a xs ih =>
      cases ys with
      | nil =>
          simp only [addCarry, toNat_cons, ih, toNat_nil]
          have h := fullAdder_correct a false c
          simp only [bitVal_false, add_zero] at h
          omega
      | cons b ys =>
          simp only [addCarry, toNat_cons, ih]
          have h := fullAdder_correct a b c
          omega

@[simp]
theorem toNat_add (xs ys : List Bool) :
    toNat (add xs ys) = toNat xs + toNat ys := by
  simp [add, toNat_addCarry]

theorem length_carryAdd (c : Bool) (ys : List Bool) :
    (carryAdd c ys).length ≤ ys.length + 1 := by
  induction ys generalizing c with
  | nil => cases c <;> simp [carryAdd]
  | cons b bs ih =>
      simp only [carryAdd, List.length_cons]
      have h := ih (carryBit false b c)
      omega

theorem length_addCarry (c : Bool) (xs ys : List Bool) :
    (addCarry c xs ys).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing c ys with
  | nil => simpa [addCarry] using length_carryAdd c ys
  | cons a xs ih =>
      cases ys with
      | nil =>
          simp only [addCarry, List.length_cons, List.length_nil, Nat.max_zero]
          have h := ih (carryBit a false c) []
          simp only [List.length_nil, Nat.max_zero] at h
          omega
      | cons b ys =>
          simp only [addCarry, List.length_cons]
          have h := ih (carryBit a b c) ys
          omega

theorem length_add (xs ys : List Bool) :
    (add xs ys).length ≤ max xs.length ys.length + 1 :=
  length_addCarry false xs ys

/-- Shift-and-add multiplication; no natural-number arithmetic is executed
by this data routine. Leading zero bits are allowed in its output. -/
def mul : List Bool → List Bool → List Bool
  | [], _ => []
  | b :: bs, ys =>
      let shifted := false :: mul bs ys
      if b then add ys shifted else shifted

@[simp]
theorem toNat_mul (xs ys : List Bool) :
    toNat (mul xs ys) = toNat xs * toNat ys := by
  induction xs with
  | nil => simp [mul]
  | cons b bs ih =>
      cases b <;> simp [mul, ih] <;> ring

/-- A deliberately loose output-width bound that needs no normalization. -/
theorem length_mul (xs ys : List Bool) :
    (mul xs ys).length ≤ 2 * xs.length + ys.length := by
  induction xs with
  | nil => simp [mul]
  | cons b bs ih =>
      cases b with
      | false => simp only [mul, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      | true =>
          simp only [mul, ↓reduceIte]
          have h := length_add ys (false :: mul bs ys)
          simp only [List.length_cons] at h ⊢
          omega

open SubexponentialSAT.Computation

/-- Three bit stacks and a three-valued finite control register. -/
structure AddCfg where
  control : Option Bool
  left : List Bool
  right : List Bool
  output : List Bool

def addStart (carry : Bool) (xs ys output : List Bool) : AddCfg :=
  ⟨some carry, xs, ys, output⟩

def addDone (output : List Bool) : AddCfg := ⟨none, [], [], output⟩

/-- One fixed-size block consumes at most one bit from each input and pushes
one result bit. No length, toNat, or natural arithmetic is evaluated here. -/
def addStep : AddCfg → Option AddCfg
  | ⟨none, _, _, _⟩ => none
  | ⟨some c, [], [], out⟩ => some (addDone (if c then true :: out else out))
  | ⟨some c, [], b :: ys, out⟩ =>
      some (addStart (carryBit false b c) [] ys (sumBit false b c :: out))
  | ⟨some c, a :: xs, [], out⟩ =>
      some (addStart (carryBit a false c) xs [] (sumBit a false c :: out))
  | ⟨some c, a :: xs, b :: ys, out⟩ =>
      some (addStart (carryBit a b c) xs ys (sumBit a b c :: out))

theorem carryAdd_trace (c : Bool) (ys out : List Bool) :
    Trace addStep (ys.length + 1) (addStart c [] ys out)
      (addDone ((carryAdd c ys).reverse ++ out)) := by
  induction ys generalizing c out with
  | nil =>
      cases c with
      | false =>
          have hs : addStep (addStart false [] [] out) = some (addDone out) := by
            simp [addStep, addStart, addDone]
          simpa [carryAdd] using Trace.cons hs (Trace.refl (addDone out))
      | true =>
          have hs : addStep (addStart true [] [] out) = some (addDone (true :: out)) := by
            simp [addStep, addStart, addDone]
          simpa [carryAdd] using Trace.cons hs (Trace.refl (addDone (true :: out)))
  | cons b ys ih =>
      have hs : addStep (addStart c [] (b :: ys) out) =
          some (addStart (carryBit false b c) [] ys (sumBit false b c :: out)) := rfl
      simpa [carryAdd, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons hs (ih (carryBit false b c) (sumBit false b c :: out))

/-- Exact number of executed stack blocks, not a cost annotation on toNat. -/
theorem add_trace (c : Bool) (xs ys out : List Bool) :
    Trace addStep (max xs.length ys.length + 1) (addStart c xs ys out)
      (addDone ((addCarry c xs ys).reverse ++ out)) := by
  induction xs generalizing c ys out with
  | nil => simpa [addCarry] using carryAdd_trace c ys out
  | cons a xs ih =>
      cases ys with
      | nil =>
          have hs : addStep (addStart c (a :: xs) [] out) =
              some (addStart (carryBit a false c) xs [] (sumBit a false c :: out)) := rfl
          simpa [addCarry, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
            Trace.cons hs (ih (carryBit a false c) [] (sumBit a false c :: out))
      | cons b ys =>
          have hs : addStep (addStart c (a :: xs) (b :: ys) out) =
              some (addStart (carryBit a b c) xs ys (sumBit a b c :: out)) := rfl
          simpa [addCarry, List.reverse_cons, List.append_assoc, Nat.add_assoc,
            max_add_add_right] using
            Trace.cons hs (ih (carryBit a b c) ys (sumBit a b c :: out))

/-! A fixed finite TM2 program implementing exactly those adder blocks. -/

abbrev AddRegisters := Bool × Option Bool × Option Bool

def cleanRegisters (c : Bool) : AddRegisters := (c, none, none)

def addProgram : Turing.TM2.Stmt (fun _ : Fin 3 => Bool) Unit AddRegisters :=
  .pop 0 (fun r a => (r.1, a, r.2.2))
    (.pop 1 (fun r b => (r.1, r.2.1, b))
      (.branch (fun r => r.2.1.isNone && r.2.2.isNone)
        (.branch (fun r => r.1)
          (.push 2 (fun _ => true) (.load (fun _ => cleanRegisters false) .halt))
          (.load (fun _ => cleanRegisters false) .halt))
        (.push 2 (fun r => sumBit (r.2.1.getD false) (r.2.2.getD false) r.1)
          (.load (fun r => cleanRegisters
            (carryBit (r.2.1.getD false) (r.2.2.getD false) r.1))
            (.goto (fun _ => ()))))))

def addMachine : Turing.FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := AddRegisters
  initialState := cleanRegisters false
  m := fun _ => addProgram

def addStacks (xs ys out : List Bool) (k : Fin 3) : List Bool :=
  if k = 0 then xs else if k = 1 then ys else out

@[simp] private theorem addStacks_zero (xs ys out : List Bool) :
    addStacks xs ys out 0 = xs := by simp [addStacks]

@[simp] private theorem addStacks_one (xs ys out : List Bool) :
    addStacks xs ys out 1 = ys := by simp [addStacks]

@[simp] private theorem addStacks_two (xs ys out : List Bool) :
    addStacks xs ys out 2 = out := by simp [addStacks]

def addEmbed (c : AddCfg) : addMachine.Cfg :=
  ⟨c.control.map (fun _ => ()), cleanRegisters (c.control.getD false),
    addStacks c.left c.right c.output⟩

@[simp] private theorem addStacks_update_left (xs ys out next : List Bool) :
    Function.update (addStacks xs ys out) 0 next = addStacks next ys out := by
  funext k
  fin_cases k <;> simp [addStacks]

@[simp] private theorem addStacks_update_right (xs ys out next : List Bool) :
    Function.update (addStacks xs ys out) 1 next = addStacks xs next out := by
  funext k
  fin_cases k <;> simp [addStacks]

@[simp] private theorem addStacks_update_output (xs ys out next : List Bool) :
    Function.update (addStacks xs ys out) 2 next = addStacks xs ys next := by
  funext k
  fin_cases k <;> simp [addStacks]

theorem add_machine_step (c : AddCfg) :
    addMachine.step (addEmbed c) = (addStep c).map addEmbed := by
  rcases c with ⟨state, xs, ys, out⟩
  cases state with
  | none => rfl
  | some carry =>
      cases xs <;> cases ys <;> cases carry <;>
        simp [addMachine, addEmbed, addProgram, Turing.TM2.step, Turing.TM2.stepAux,
          cleanRegisters, addStep, addStart, addDone, Option.map_some] <;>
        congr 3 <;> funext k <;> fin_cases k <;> rfl

theorem add_machine_trace {n : ℕ} {a b : AddCfg} (h : Trace addStep n a b) :
    Trace addMachine.step n (addEmbed a) (addEmbed b) := by
  induction h with
  | refl a => exact Trace.refl _
  | cons hs ht ih =>
      apply Trace.cons _ ih
      rw [add_machine_step, hs]
      rfl

/-- The finite stack machine executes a linear number of its fixed blocks. -/
theorem addMachine_correct (c : Bool) (xs ys : List Bool) :
    Trace addMachine.step (max xs.length ys.length + 1)
      (addEmbed (addStart c xs ys []))
      (addEmbed (addDone (addCarry c xs ys).reverse)) := by
  simpa using add_machine_trace (add_trace c xs ys [])

theorem addMachine_blockOverhead :
    SubexponentialSAT.FixedParameters.blockOverhead addMachine = 12 := by
  decide

/-- Expanding the fixed blocks gives a measured trace of actual one-constructor
stack operations. A stack-to-primitive-tape compiler is still separate. -/
theorem addMachine_micro_correct (c : Bool) (xs ys : List Bool) :
    RunsIn (SubexponentialSAT.FixedParameters.microStep addMachine)
      (12 * (max xs.length ys.length + 1))
      (SubexponentialSAT.FixedParameters.embed addMachine (addEmbed (addStart c xs ys [])))
      (SubexponentialSAT.FixedParameters.embed addMachine
        (addEmbed (addDone (addCarry c xs ys).reverse))) := by
  have hrun : RunsIn addMachine.step (max xs.length ys.length + 1)
      (addEmbed (addStart c xs ys []))
      (addEmbed (addDone (addCarry c xs ys).reverse)) :=
    ⟨_, le_rfl, addMachine_correct c xs ys⟩
  simpa only [addMachine_blockOverhead] using
    SubexponentialSAT.FixedParameters.micro_execution addMachine hrun

/-! Source-level bit-event traces for the recursive multiplication routine.
The lists below record inspections, Boolean gates, and constructed list cells.
They are not asserted to be PrimitiveMachine execution traces. -/

inductive BitEvent
  | inspect
  | gate
  | push
  | control
  deriving DecidableEq

def fullAdderEvents : List BitEvent :=
  [.gate, .gate, .gate, .gate, .gate, .gate, .gate]

def carryEvents (c : Bool) : List Bool → List BitEvent
  | [] => if c then [.inspect, .push] else [.inspect]
  | b :: bs => [.inspect] ++ fullAdderEvents ++ [.push] ++
      carryEvents (carryBit false b c) bs

def addEvents (c : Bool) : List Bool → List Bool → List BitEvent
  | [], ys => .inspect :: carryEvents c ys
  | a :: xs, [] => [.inspect, .inspect] ++ fullAdderEvents ++ [.push] ++
      addEvents (carryBit a false c) xs []
  | a :: xs, b :: ys => [.inspect, .inspect] ++ fullAdderEvents ++ [.push] ++
      addEvents (carryBit a b c) xs ys

theorem length_carryEvents (c : Bool) (ys : List Bool) :
    (carryEvents c ys).length ≤ 10 * (ys.length + 1) := by
  induction ys generalizing c with
  | nil => cases c <;> simp [carryEvents]
  | cons b bs ih =>
      simp only [carryEvents, List.length_append, List.length_cons, List.length_nil]
      have h := ih (carryBit false b c)
      change 1 + 7 + 1 + _ ≤ _
      omega

theorem length_addEvents (c : Bool) (xs ys : List Bool) :
    (addEvents c xs ys).length ≤ 12 * (max xs.length ys.length + 1) := by
  induction xs generalizing c ys with
  | nil =>
      simp only [addEvents, List.length_cons, List.length_nil, Nat.zero_max]
      have h := length_carryEvents c ys
      omega
  | cons a xs ih =>
      cases ys with
      | nil =>
          simp only [addEvents, List.length_append, List.length_cons, List.length_nil,
            Nat.max_zero]
          have h := ih (carryBit a false c) []
          simp only [List.length_nil, Nat.max_zero] at h
          change 2 + 7 + 1 + _ ≤ _
          omega
      | cons b ys =>
          simp only [addEvents, List.length_append, List.length_cons, List.length_nil]
          have h := ih (carryBit a b c) ys
          change 2 + 7 + 1 + _ ≤ _
          omega

def mulEvents : List Bool → List Bool → List BitEvent
  | [], _ => [.inspect]
  | b :: bs, ys =>
      [.inspect, .control] ++ mulEvents bs ys ++ [.push, .control] ++
        if b then addEvents false ys (false :: mul bs ys) else []

/-- Executable writer-style interpretation: result bits and primitive source
events are produced together, without using natural-number arithmetic. -/
def carryAddRun (c : Bool) : List Bool → List Bool × List BitEvent
  | [] => if c then ([true], [.inspect, .push]) else ([], [.inspect])
  | b :: bs =>
      let r := carryAddRun (carryBit false b c) bs
      (sumBit false b c :: r.1, [.inspect] ++ fullAdderEvents ++ [.push] ++ r.2)

def addRun (c : Bool) : List Bool → List Bool → List Bool × List BitEvent
  | [], ys =>
      let r := carryAddRun c ys
      (r.1, .inspect :: r.2)
  | a :: xs, [] =>
      let r := addRun (carryBit a false c) xs []
      (sumBit a false c :: r.1,
        [.inspect, .inspect] ++ fullAdderEvents ++ [.push] ++ r.2)
  | a :: xs, b :: ys =>
      let r := addRun (carryBit a b c) xs ys
      (sumBit a b c :: r.1,
        [.inspect, .inspect] ++ fullAdderEvents ++ [.push] ++ r.2)

def mulRun : List Bool → List Bool → List Bool × List BitEvent
  | [], _ => ([], [.inspect])
  | b :: bs, ys =>
      let r := mulRun bs ys
      if b then
        let s := addRun false ys (false :: r.1)
        (s.1, [.inspect, .control] ++ r.2 ++ [.push, .control] ++ s.2)
      else
        (false :: r.1, [.inspect, .control] ++ r.2 ++ [.push, .control])

theorem carryAddRun_eq (c : Bool) (ys : List Bool) :
    carryAddRun c ys = (carryAdd c ys, carryEvents c ys) := by
  induction ys generalizing c with
  | nil => cases c <;> rfl
  | cons b bs ih => simp [carryAddRun, carryAdd, carryEvents, ih]

theorem addRun_eq (c : Bool) (xs ys : List Bool) :
    addRun c xs ys = (addCarry c xs ys, addEvents c xs ys) := by
  induction xs generalizing c ys with
  | nil => simp [addRun, addCarry, addEvents, carryAddRun_eq]
  | cons a xs ih =>
      cases ys <;> simp [addRun, addCarry, addEvents, ih]

theorem mulRun_eq (xs ys : List Bool) :
    mulRun xs ys = (mul xs ys, mulEvents xs ys) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [mulRun, mul, mulEvents, ih, addRun_eq, add]

theorem length_mulEvents (xs ys : List Bool) :
    (mulEvents xs ys).length ≤ 40 * (xs.length + 1) * (xs.length + ys.length + 1) := by
  induction xs with
  | nil => simp [mulEvents]; omega
  | cons b bs ih =>
      have hw := length_mul bs ys
      cases b with
      | false =>
          simp only [mulEvents, Bool.false_eq_true, ↓reduceIte, List.length_append,
            List.length_cons, List.length_nil]
          nlinarith
      | true =>
          have ha := length_addEvents false ys (false :: mul bs ys)
          have hm : max ys.length (false :: mul bs ys).length ≤
              2 * bs.length + ys.length + 1 := by
            simp only [List.length_cons]
            omega
          simp only [mulEvents, ↓reduceIte, List.length_append,
            List.length_cons, List.length_nil]
          nlinarith

theorem addRun_correct_and_cost (c : Bool) (xs ys : List Bool) :
    toNat (addRun c xs ys).1 = toNat xs + toNat ys + bitVal c ∧
    (addRun c xs ys).2.length ≤ 12 * (max xs.length ys.length + 1) := by
  rw [addRun_eq]
  exact ⟨toNat_addCarry c xs ys, length_addEvents c xs ys⟩

theorem mulRun_correct_and_cost (xs ys : List Bool) :
    toNat (mulRun xs ys).1 = toNat xs * toNat ys ∧
    (mulRun xs ys).2.length ≤ 40 * (xs.length + 1) * (xs.length + ys.length + 1) := by
  rw [mulRun_eq]
  exact ⟨toNat_mul xs ys, length_mulEvents xs ys⟩

end SubexponentialSAT.BinaryArithmetic

end OAI.Algorithms
