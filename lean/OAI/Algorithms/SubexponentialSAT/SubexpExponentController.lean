import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentSuccessor
import OAI.Algorithms.SubexponentialSAT.SubexpExponentOrder
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Fixed-control bounded-exponent emission

The current reversed unary exponent word and the remaining degree budget are
runtime stacks.  Emitting a word copies and frames it using existing concrete
stack routines.  The loop then invokes the verified budget-spending successor.
There is no table of candidate vectors in the instruction control.
-/

namespace SubexponentialSAT.SubexpExponentController

open scoped BigOperators
open BitProgram StructuredCalls
open SubexpExponentSuccessor

abbrev Data := StructuredProgram.State 3 6
abbrev Code := StructuredCalls.Cmd 3 6

def storage6 (digits budget pending output buffer temporary : List Bool) :
    Fin 6 → List Bool := ![digits, budget, pending, output, buffer, temporary]

def state (regs : Fin 3 → Bool)
    (digits budget pending output buffer temporary : List Bool) : Data :=
  ⟨regs, storage6 digits budget pending output buffer temporary⟩

def encoded (regs : Fin 3 → Bool) (digits : List ℕ) (budget pending : ℕ)
    (output : List Bool) : Data :=
  state regs (digitsCode digits) (List.replicate budget true)
    (List.replicate pending false) output [] []

theorem digitsCode_length (digits : List ℕ) :
    (digitsCode digits).length = digits.length + digits.sum := by
  induction digits with
  | nil => rfl
  | cons a digits ih =>
    simp only [digitsCode_cons, List.length_cons, List.length_append,
      List.length_replicate, List.sum_cons, ih]
    omega

def nextPorts (i : Fin 3) : Fin 6 := Fin.castAdd 3 i

theorem nextPorts_injective : Function.Injective nextPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 6 => i.val) h)

def nextCall : Code :=
  .call (ProgramLinking.liftProgram nextProgram id nextPorts)

private theorem head_embed (frameRegs regs : Fin 3 → Bool)
    (x y z x' y' z' out buf tmp : List Bool) :
    embedState id nextPorts (state frameRegs x y z out buf tmp)
      ⟨regs, SubexpExponentSuccessor.storage x' y' z'⟩ =
        state regs x' y' z' out buf tmp := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id nextPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · rfl
    · rfl
    · rfl

theorem nextCall_eval (digits : List ℕ) (budget pending : ℕ)
    (regs : Fin 3 → Bool) (output : List Bool) :
    ∃ finalRegs, finalRegs 2 = (nextResult digits budget pending).found ∧
      Eval nextCall (nextResult digits budget pending).ticks
        (encoded regs digits budget pending output)
        (encoded finalRegs (nextResult digits budget pending).digits
          (nextResult digits budget pending).budget
          (nextResult digits budget pending).pending output) := by
  obtain ⟨finalRegs, hflag, ht⟩ := next_trace digits budget pending regs
  refine ⟨finalRegs, hflag, ?_⟩
  change Trace nextProgram (nextResult digits budget pending).ticks
    ((⟨regs, SubexpExponentSuccessor.storage (digitsCode digits)
      (List.replicate budget true) (List.replicate pending false)⟩ :
        StructuredProgram.State 3 3).withPC (some nextProgram.entry))
    ((⟨finalRegs, SubexpExponentSuccessor.storage
      (digitsCode (nextResult digits budget pending).digits)
      (List.replicate (nextResult digits budget pending).budget true)
      (List.replicate (nextResult digits budget pending).pending false)⟩ :
        StructuredProgram.State 3 3).withPC none) at ht
  have h := eval_call_lifted nextProgram id nextPorts
    (encoded regs digits budget pending output)
    Function.injective_id nextPorts_injective ht
  simpa only [nextCall, encoded, head_embed] using h

def emitterPorts : Fin 4 → Fin 6 := ![0, 1, 3, 4]

theorem emitterPorts_injective : Function.Injective emitterPorts := by decide

def frameCall : Code := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram id emitterPorts)

def emittedRegs (regs : Fin 3 → Bool) : Fin 3 → Bool := ![true, false, regs 2]

private theorem writer_embed (frameRegs : Fin 3 → Bool)
    (v p selected : Bool) (x₀ y₀ out₀ buf₀ x y z out buf tmp : List Bool) :
    embedState id emitterPorts (state frameRegs x₀ y₀ z out₀ buf₀ tmp)
      (SubexpNormalizeProgram.filterState v p selected x y out buf) =
        state ![v, p, selected] x y z out buf tmp := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id emitterPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · rfl
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · rfl

private theorem regs_eta (regs : Fin 3 → Bool) : ![regs 0, regs 1, regs 2] = regs := by
  funext i; fin_cases i <;> rfl

theorem frameCall_eval (regs : Fin 3 → Bool)
    (digits budget pending output temporary bits : List Bool) :
    Eval frameCall (5 * bits.length + 7)
      (state regs digits budget pending output bits.reverse temporary)
      (state (emittedRegs regs) digits budget pending
        (true :: (Encoding.frame bits ++ output)) [] temporary) := by
  have ht := SubexpNormalizeProgram.emitRecord_trace bits digits budget output
    (regs 0) (regs 1) (regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram id emitterPorts
    (state regs digits budget pending output bits.reverse temporary)
    Function.injective_id emitterPorts_injective ht
  simpa only [frameCall, writer_embed, regs_eta, emittedRegs] using h

def emit : Code := .seq
  (.call (StackRoutines.copyProgram 0 4 5 0 1)) frameCall

theorem emit_eval (digits : List ℕ) (budget pending : ℕ)
    (regs : Fin 3 → Bool) (output : List Bool) :
    Eval emit (12 * (digitsCode digits).length + 12)
      (encoded regs digits budget pending output)
      (encoded (emittedRegs regs) digits budget pending
        (true :: (Encoding.frame (digitsCode digits).reverse ++ output))) := by
  let middle := readRegs regs 0 1 none
  have hcopy := ListRegisterProgram.copy_run (0 : Fin 6) 4 5 (0 : Fin 3) 1
    (by decide) (by decide) (by decide) (by decide) regs
    (storage6 (digitsCode digits) (List.replicate budget true)
      (List.replicate pending false) output [] []) (by rfl)
  have hst : StackRoutines.copyStacks (0 : Fin 6) 4
      (storage6 (digitsCode digits) (List.replicate budget true)
        (List.replicate pending false) output [] []) =
      storage6 (digitsCode digits) (List.replicate budget true)
        (List.replicate pending false) output (digitsCode digits) [] := by
    funext i; fin_cases i <;> simp [StackRoutines.copyStacks, storage6]
  have hlen :
      (storage6 (digitsCode digits) (List.replicate budget true)
        (List.replicate pending false) output [] [] 0).length =
        (digitsCode digits).length := rfl
  have h₁ : Eval (.call (StackRoutines.copyProgram 0 4 5 0 1))
      (7 * (digitsCode digits).length + 5)
      (encoded regs digits budget pending output)
      (state middle (digitsCode digits) (List.replicate budget true)
        (List.replicate pending false) output (digitsCode digits) []) := by
    apply Eval.call
    simpa only [ListRegisterProgram.Run, encoded, state, StructuredProgram.State.withPC,
      hst, hlen, middle] using hcopy
  have h₂ := frameCall_eval middle (digitsCode digits) (List.replicate budget true)
    (List.replicate pending false) output [] (digitsCode digits).reverse
  have he : emittedRegs middle = emittedRegs regs := by
    simp [emittedRegs, middle, readRegs]
  have total := h₁.seq (by simpa only [List.reverse_reverse] using h₂)
  simpa only [emit, List.length_reverse, he, encoded,
    show (7 * (digitsCode digits).length + 5) +
      (5 * (digitsCode digits).length + 7) =
      12 * (digitsCode digits).length + 12 by omega] using total

def body : Code := .seq emit nextCall

def loop : Code := .while 2 body

def initializer : Code := .seq (.base (.atom (.set 0 false)))
  (.seq (.base (.atom (.push 3 0))) (.base (.atom (.set 2 true))))

/-- A fixed program writes the list terminator and starts the emission loop.
The input coordinate word has one false marker per coordinate; the budget
is on stack 1.  A complete source-order proof is supplied separately by the
successor visitation theorem. -/
def controller : Code := .seq initializer loop

def program := StructuredCalls.compiled controller 0 3

def momentBits (s : SubexpExponentOrder.State) : List Bool :=
  (digitsCode s.1).reverse

def collected : List SubexpExponentOrder.State → List Bool → List Bool
  | [], output => output
  | s :: rest, output => collected rest (true :: (Encoding.frame (momentBits s) ++ output))

def visitsCost : List SubexpExponentOrder.State → ℕ
  | [] => 1
  | s :: rest => 12 * (digitsCode s.1).length + 12 +
      (nextResult s.1 s.2 0).ticks + visitsCost rest + 1

/-- The concrete loop visits exactly the supplied successor trace.  Its only
premise about iteration is the inductive relation whose one step is the
explicit `nextDigits` function; the complete exponent-list instance below
discharges that premise. -/
theorem loop_eval (digits : List ℕ) (budget : ℕ)
    (observed : List SubexpExponentOrder.State)
    (visits : SubexpExponentOrder.Visits (some (digits, budget)) observed none)
    (regs : Fin 3 → Bool) (output : List Bool) (hstart : regs 2 = true) :
    ∃ finalRegs, finalRegs 2 = false ∧
      Eval loop (visitsCost observed) (encoded regs digits budget 0 output)
        (encoded finalRegs [] (budget + digits.sum) digits.length (collected observed output)) := by
  induction observed generalizing digits budget regs output with
  | nil => cases visits
  | cons s rest ih =>
    cases visits with
    | cons current tail =>
      let newOut := true :: (Encoding.frame (digitsCode digits).reverse ++ output)
      have hemit := emit_eval digits budget 0 regs output
      obtain ⟨middleRegs, hflag, hnext⟩ :=
        nextCall_eval digits budget 0 (emittedRegs regs) newOut
      have hbody : Eval body
          (12 * (digitsCode digits).length + 12 + (nextResult digits budget 0).ticks)
          (encoded regs digits budget 0 output)
          (encoded middleRegs (nextResult digits budget 0).digits
            (nextResult digits budget 0).budget (nextResult digits budget 0).pending newOut) :=
        hemit.seq hnext
      cases hn : nextDigits digits budget with
      | none =>
        rw [hn] at tail
        cases tail
        have hs := nextResult_spec digits budget 0
        rw [hn] at hs
        rcases hs with ⟨hd, hb, hp, hf⟩
        simp only [Nat.zero_add] at hp
        rw [hd, hb, hp] at hbody
        have hfalse : middleRegs 2 = false := hflag.trans hf
        have hstop : Eval loop 1
            (encoded middleRegs [] (budget + digits.sum) digits.length newOut)
            (encoded middleRegs [] (budget + digits.sum) digits.length newOut) :=
          .while_false hfalse
        refine ⟨middleRegs, hfalse, ?_⟩
        simpa only [loop, visitsCost, collected, momentBits, newOut] using
          Eval.while_true hstart hbody hstop
      | some pair =>
        rcases pair with ⟨next, remaining⟩
        rw [hn] at tail
        rcases nextResult_success hn with ⟨hd, hb, hp, hf⟩
        rw [hd, hb, hp] at hbody
        have htrue : middleRegs 2 = true := hflag.trans hf
        obtain ⟨finalRegs, hfinal, hrest⟩ := ih next remaining tail middleRegs newOut htrue
        have hlen := nextDigits_length hn
        have hsum : remaining + next.sum = budget + digits.sum := by
          have hs := nextDigits_budget hn
          omega
        rw [hlen, hsum] at hrest
        refine ⟨finalRegs, hfinal, ?_⟩
        simpa only [loop, visitsCost, collected, momentBits, newOut] using
          Eval.while_true hstart hbody hrest

theorem collected_eq (observed : List SubexpExponentOrder.State) (output : List Bool) :
    collected observed output =
      observed.reverse.flatMap (fun s => true :: Encoding.frame (momentBits s)) ++ output := by
  induction observed generalizing output with
  | nil => simp [collected]
  | cons s rest ih => simp [collected, ih, List.flatMap_append, List.append_assoc]

theorem collected_terminated (observed : List SubexpExponentOrder.State) :
    collected observed [false] = Encoding.encodeList momentBits observed.reverse := by
  rw [collected_eq]
  generalize observed.reverse = xs
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    simpa [Encoding.encodeList, List.append_assoc] using
      (congrArg (fun tail => true :: (Encoding.frame (momentBits s) ++ tail)) ih)

theorem visitsCost_le (observed : List SubexpExponentOrder.State) (D N : ℕ)
    (bounds : ∀ s ∈ observed, s.1.length = D ∧ s.1.sum ≤ N) :
    visitsCost observed ≤ 25 * (D + N + 1) * observed.length + 1 := by
  induction observed with
  | nil => simp [visitsCost]
  | cons s rest ih =>
    have hs := bounds s (by simp)
    have ht := ih (fun v hv => bounds v (by simp [hv]))
    have hn := nextResult_ticks_le s.1 s.2 0
    simp only [visitsCost, digitsCode_length, List.length_cons]
    rw [hs.1]
    simp only [Nat.mul_zero, Nat.add_zero, hs.1] at hn
    simp only [Nat.mul_add, Nat.mul_one] at ht ⊢
    omega

def initializedRegs (regs : Fin 3 → Bool) : Fin 3 → Bool :=
  Function.update (Function.update regs 0 false) 2 true

theorem initialize_eval (regs : Fin 3 → Bool) (digits : List ℕ) (budget : ℕ) :
    Eval initializer 3 (encoded regs digits budget 0 [])
      (encoded (initializedRegs regs) digits budget 0 [false]) := by
  let a := encoded regs digits budget 0 []
  let first : StructuredProgram.Atom 3 6 := .set 0 false
  let second : StructuredProgram.Atom 3 6 := .push 3 0
  let third : StructuredProgram.Atom 3 6 := .set 2 true
  have ht : Eval initializer 3 a (third.eval (second.eval (first.eval a))) :=
    .seq (.base (.atom first a))
      (.seq (.base (.atom second (first.eval a)))
        (.base (.atom third (second.eval (first.eval a)))))
  have he : third.eval (second.eval (first.eval a)) =
      encoded (initializedRegs regs) digits budget 0 [false] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;>
        simp [third, second, first, a, StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
          execInstr, encoded, state, initializedRegs]
    · funext i; fin_cases i <;>
        simp [third, second, first, a, StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
          execInstr, encoded, state, storage6]
  simpa only [a, he] using ht

def observations (D N : ℕ) : List SubexpExponentOrder.State :=
  (Algorithm.exponentList D N).map fun a => ((List.ofFn a).reverse, N - ∑ i, a i)

def momentWord {D : ℕ} (a : Fin D → ℕ) : List Bool :=
  SymbolicCost.unaryWords (List.ofFn a)

theorem momentBits_observation {D N : ℕ} (a : Fin D → ℕ) :
    momentBits ((List.ofFn a).reverse, N - ∑ i, a i) = momentWord a := by
  simp [momentBits, digitsCode_reverse_unary, momentWord]

theorem observation_output (D N : ℕ) :
    collected (observations D N) [false] =
      Encoding.encodeList momentWord (Algorithm.exponentList D N).reverse := by
  rw [collected_terminated]
  unfold observations
  rw [← List.map_reverse]
  generalize (Algorithm.exponentList D N).reverse = xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [Encoding.encodeList, momentBits_observation, ih]

theorem observations_cost (D N : ℕ) :
    visitsCost (observations D N) ≤
      25 * (D + N + 1) * (D + N).choose D + 1 := by
  have hb (s : SubexpExponentOrder.State) (hs : s ∈ observations D N) :
      s.1.length = D ∧ s.1.sum ≤ N := by
    obtain ⟨hl, hsum⟩ := SubexpExponentOrder.observation_bounds hs
    exact ⟨hl, by omega⟩
  simpa only [observations, List.length_map, Algorithm.exponentList_length] using
    visitsCost_le (observations D N) D N hb

/-- The actual fixed controller emits every bounded-total-degree exponent
exactly once. Record order is reversed because the frame writer prepends. -/
theorem controller_eval (D N : ℕ) (regs : Fin 3 → Bool) :
    ∃ finalRegs, finalRegs 2 = false ∧
      Eval controller (3 + visitsCost (observations D N))
        (encoded regs (List.replicate D 0) N 0 [])
        (encoded finalRegs [] N D
          (Encoding.encodeList momentWord (Algorithm.exponentList D N).reverse)) := by
  have hi := initialize_eval regs (List.replicate D 0) N
  obtain ⟨finalRegs, hf, hl⟩ := loop_eval (List.replicate D 0) N (observations D N)
    (SubexpExponentOrder.exponentList_visits D N) (initializedRegs regs) [false]
    (by simp [initializedRegs])
  refine ⟨finalRegs, hf, ?_⟩
  simpa [controller, observation_output] using hi.seq hl

/-- One finite instruction table works for every dimension and degree bound.
The measured count grows with the number of valid vectors, with a linear
factor for writing each unary key and advancing its coordinate stack. -/
theorem controller_runsIn (D N : ℕ) (regs : Fin 3 → Bool) :
    ∃ finalRegs, finalRegs 2 = false ∧
      RunsIn program (25 * (D + N + 1) * (D + N).choose D + 5)
        ((encoded regs (List.replicate D 0) N 0 []).withPC (some program.entry))
        ((encoded finalRegs [] N D
          (Encoding.encodeList momentWord (Algorithm.exponentList D N).reverse)).withPC none) := by
  obtain ⟨finalRegs, hf, he⟩ := controller_eval D N regs
  have ht := StructuredCalls.compiled_halt_trace he 0 3
  refine ⟨finalRegs, hf, _, ?_, ht⟩
  have hb := observations_cost D N
  omega

end SubexponentialSAT.SubexpExponentController

end OAI.Algorithms
