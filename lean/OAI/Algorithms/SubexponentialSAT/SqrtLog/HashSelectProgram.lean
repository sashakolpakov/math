import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramRound
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramGenerate
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectList

namespace OAI.Algorithms

/-! A fixed deterministic hash selector. Its input carries a unary round
counter and a saved candidate queue. Every round copies that queue, pays
for every mass evaluation, takes a binary argmin, and appends the winner.
The only computational premise is the explicit trace specification of the
mass subprogram; no semantic SAT or mass instruction occurs in the code. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

variable {r s : ℕ}

structure ControllerPorts (r s : ℕ) where
  trial : RoundPorts r s
  loop : LoopPorts r s
  counter_outside : ∀ i, trial.core.stack i ≠ loop.counter
  value_outside : ∀ i, trial.core.register i ≠ loop.value
  present_outside : ∀ i, trial.core.register i ≠ loop.present
  rows_ne_counter : trial.rows ≠ loop.counter
  family_ne_counter : trial.family ≠ loop.counter
  family_ne_rows : trial.family ≠ trial.rows

/-- The untouched input banks retain their initial values between rounds. -/
def ControllerReady (p : ControllerPorts r s) (frame : State r s)
    (family rows : Records) (a : State r s) : Prop :=
  (∀ i, a.stacks (p.trial.core.stack i) = []) ∧
  a.stacks p.trial.family = candidateEncoding family ∧
  a.stacks p.trial.rows = candidateEncoding rows ∧
  (∀ i, i ≠ p.trial.rows → i ≠ p.loop.counter →
    (∀ j, p.trial.core.stack j ≠ i) → a.stacks i = frame.stacks i) ∧
  (∀ i, i ≠ p.loop.value → i ≠ p.loop.present →
    (∀ j, p.trial.core.register j ≠ i) → a.regs i = frame.regs i)

def payloadNext (score : Records → List Bool → List Bool)
    (seed : List Bool) (rest : Records) (rows : Records) : Records :=
  HashSelect.best (fun bits => BinaryArithmetic.toNat (score rows bits)) seed rest :: rows

abbrev controller (p : ControllerPorts r s) (mass : Cmd r s) : Cmd r s :=
  rounds p.loop (round p.trial mass)

def controllerBudget (B C cost familyBits count rounds : ℕ) : ℕ :=
  roundsBudget (roundBudget B C cost familyBits count) rounds

theorem ready_read (p : ControllerPorts r s) (frame : State r s)
    (family rows : Records) (a : State r s) (h : ControllerReady p frame family rows a) :
    ControllerReady p frame family rows (readCounterState p.loop a) := by
  rcases h with ⟨he, hf, hr, hs, hg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [readCounterState, p.counter_outside i] using he i
  · simpa [readCounterState, p.family_ne_counter] using hf
  · simpa [readCounterState, p.rows_ne_counter] using hr
  · intro i hi hc hout
    simpa [readCounterState, hc] using hs i hi hc hout
  · intro i hv hp hout
    simpa [readCounterState, readRegs, hv, hp] using hg i hv hp hout

/-- The concrete round establishes the loop specification. All calls,
including failed candidates and the initial candidate, are charged. -/
theorem controller_roundSpec (p : ControllerPorts r s) (mass : Cmd r s)
    (frame : State r s) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest : Records)
    (hmass : ∀ rows a, ControllerReady p frame (seed :: rest) rows a →
      MassSpec mass p.trial.core (afterCopyFamily p.trial a)
        (score rows) (valid rows) B C cost)
    (hp : ∀ rows, ∀ bits ∈ seed :: rest,
      valid rows bits ∧ bits.length ≤ C ∧ (score rows bits).length = B) :
    RoundSpec p.loop (round p.trial mass) (payloadNext score seed rest)
      (ControllerReady p frame (seed :: rest))
      (roundBudget B C cost (candidateEncoding (seed :: rest)).length (rest.length + 1)) := by
  constructor
  · exact ready_read p frame (seed :: rest)
  · intro rows a hready hguard
    obtain ⟨n, hn, b, ht, he, hr, hs, hg⟩ := round_eval_ready p.trial mass a
      (score rows) (valid rows) B C cost (hmass rows a hready)
      seed rest hready.1 hready.2.1 (hp rows)
    refine ⟨n, ?_, b, ?_, ?_, ?_, ht⟩
    · simpa [hready.2.1] using hn
    · refine ⟨he, ?_, ?_, ?_, ?_⟩
      · exact (hs _ p.family_ne_rows p.trial.family_outside).trans hready.2.1
      · rw [best_scored] at hr
        simpa [payloadNext, candidateEncoding, scored, hready.2.2.1] using hr
      · intro i hi hc hout
        exact (hs i hi hout).trans (hready.2.2.2.1 i hi hc hout)
      · intro i hv hp hout
        exact (hg i hout).trans (hready.2.2.2.2 i hv hp hout)
    · exact hs _ (Ne.symm p.rows_ne_counter) p.counter_outside
    · exact (hg _ p.present_outside).trans hguard

theorem controller_eval (p : ControllerPorts r s) (mass : Cmd r s)
    (frame : State r s) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest rows : Records) (depth : List Bool) (a : State r s)
    (hmass : ∀ rows a, ControllerReady p frame (seed :: rest) rows a →
      MassSpec mass p.trial.core (afterCopyFamily p.trial a)
        (score rows) (valid rows) B C cost)
    (hp : ∀ rows, ∀ bits ∈ seed :: rest,
      valid rows bits ∧ bits.length ≤ C ∧ (score rows bits).length = B)
    (ha : ControllerReady p frame (seed :: rest) rows a)
    (hd : a.stacks p.loop.counter = depth) :
    ∃ n ≤ controllerBudget B C cost (candidateEncoding (seed :: rest)).length
      (rest.length + 1) depth.length, ∃ b,
      ControllerReady p frame (seed :: rest)
        (iter (payloadNext score seed rest) depth.length rows) b ∧
      b.stacks p.loop.counter = [] ∧ b.regs p.loop.present = false ∧
      Eval (controller p mass) n a b := by
  exact rounds_eval p.loop (round p.trial mass) (payloadNext score seed rest)
    (ControllerReady p frame (seed :: rest)) _
    (controller_roundSpec p mass frame score valid B C cost seed rest hmass hp)
    rows depth a ha hd

abbrev controllerProgram (p : ControllerPorts r s) (mass : Cmd r s) :=
  compiled (controller p mass) p.loop.counter p.trial.rows

theorem controllerProgram_trace (p : ControllerPorts r s) (mass : Cmd r s)
    (frame : State r s) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest rows : Records) (depth : List Bool) (a : State r s)
    (hmass : ∀ rows a, ControllerReady p frame (seed :: rest) rows a →
      MassSpec mass p.trial.core (afterCopyFamily p.trial a)
        (score rows) (valid rows) B C cost)
    (hp : ∀ rows, ∀ bits ∈ seed :: rest,
      valid rows bits ∧ bits.length ≤ C ∧ (score rows bits).length = B)
    (ha : ControllerReady p frame (seed :: rest) rows a)
    (hd : a.stacks p.loop.counter = depth) :
    ∃ n ≤ controllerBudget B C cost (candidateEncoding (seed :: rest)).length
      (rest.length + 1) depth.length + 1, ∃ b : State r s,
      b.stacks p.trial.rows = candidateEncoding
        (iter (payloadNext score seed rest) depth.length rows) ∧
      b.stacks p.loop.counter = [] ∧
      Trace (controllerProgram p mass) n
        (a.withPC (some (controllerProgram p mass).entry)) (b.withPC none) := by
  obtain ⟨n, hn, b, hb, hc, _, ht⟩ := controller_eval p mass frame score valid
    B C cost seed rest rows depth a hmass hp ha hd
  exact ⟨n + 1, Nat.add_le_add_right hn 1, b, hb.2.2.1, hc,
    compiled_halt_trace ht _ _⟩

/-- This displays the contribution of every paid mass evaluation over K
rounds. Candidate enumeration is a separate, also traced preprocessing cost. -/
theorem controllerBudget_callback (B C cost familyBits count K : ℕ) :
    controllerBudget B C cost familyBits count K = K * (count + 1) * cost +
      K * (7 * familyBits + (count + 1) *
        (6 * C + 100 * (B + C + 1) + 14) + 5 * C + 2 * B + 17) + 2 := by
  unfold controllerBudget roundsBudget roundBudget
  rw [selectBudget_callback]
  ring

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
