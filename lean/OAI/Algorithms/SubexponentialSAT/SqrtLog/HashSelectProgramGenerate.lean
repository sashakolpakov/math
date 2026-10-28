import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramCore

namespace OAI.Algorithms

/-! Runtime-depth tuple enumeration by the audited 83-label finite controller.
The selector reads the generator's existing framed queue directly: reversing
payload interpretation accounts for the parser's stack order without a free
array conversion. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

abbrev Records := List (List Bool)

def generatedPayloads (alphabet : Records) (depth : ℕ) : Records :=
  (TupleProgram.powerRows alphabet depth [[]]).map List.reverse

theorem candidateEncoding_reverse (records : Records) :
    candidateEncoding (records.map List.reverse) = ProgramEncoding.encodeRecords records := by
  induction records with
  | nil => rfl
  | cons a rest ih =>
    simp [candidateEncoding, ProgramEncoding.encodeRecords, Encoding.encodeList, ih]

@[simp] theorem generatedPayloads_length (alphabet : Records) (depth : ℕ) :
    (generatedPayloads alphabet depth).length = alphabet.length ^ depth := by
  simp [generatedPayloads, TupleProgram.generated_count]

theorem cartesian_width (alphabet rows : Records) (a b : ℕ)
    (ha : ∀ x ∈ alphabet, x.length = a) (hb : ∀ x ∈ rows, x.length = b) :
    ∀ x ∈ TupleProgram.cartesianOutput rows alphabet, x.length = b + a := by
  intro x hx
  simp only [TupleProgram.cartesianOutput, List.mem_reverse, List.mem_flatMap] at hx
  obtain ⟨row, hr, hx⟩ := hx
  obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hx
  simp [ha word hw, hb row hr]

theorem powerRows_width (alphabet rows : Records) (a b depth : ℕ)
    (ha : ∀ x ∈ alphabet, x.length = a) (hb : ∀ x ∈ rows, x.length = b) :
    ∀ x ∈ TupleProgram.powerRows alphabet depth rows, x.length = b + depth * a := by
  induction depth generalizing rows b with
  | zero => simpa [TupleProgram.powerRows] using hb
  | succ depth ih =>
    have h := ih (TupleProgram.cartesianOutput rows alphabet) (b + a)
      (cartesian_width alphabet rows a b ha hb)
    simpa [TupleProgram.powerRows, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

theorem generatedPayloads_width (alphabet : Records) (a depth : ℕ)
    (ha : ∀ x ∈ alphabet, x.length = a) :
    ∀ x ∈ generatedPayloads alphabet depth, x.length = depth * a := by
  intro x hx
  obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hx
  have h := powerRows_width alphabet [[]] a 0 depth ha (by simp) word hw
  simpa using h

structure GeneratePorts (r s : ℕ) where
  register : Fin 10 → Fin r
  stack : Fin 9 → Fin s
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

abbrev generate {r s : ℕ} (p : GeneratePorts r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram TupleProgram.generateProgram p.register p.stack)

/-- One program for every runtime depth. Alphabet serialization and the unary
counter are input data; no tuple table is supplied for free. -/
theorem generate_eval {r s : ℕ} (p : GeneratePorts r s) (frame : State r s)
    (alphabet : Records) (depth : List Bool) (guard : Bool) (a : State 10 9)
    (ha : TupleProgram.outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ n ≤ TupleProgram.powerCost alphabet depth.length [[]] + 9,
      ∃ next : State 10 9,
        TupleProgram.Ready alphabet (TupleProgram.powerRows alphabet depth.length [[]])
          [] false next ∧
        next.stacks 0 = candidateEncoding (generatedPayloads alphabet depth.length) ∧
        Eval (generate p) n
          (embedState p.register p.stack frame a)
          (embedState p.register p.stack frame next) := by
  obtain ⟨next, hn, n, hb, ht⟩ :=
    TupleProgram.generateProgram_runsIn alphabet depth guard a ha h0 h2 h5
  refine ⟨n, hb, next, hn, ?_, ?_⟩
  · simpa [generatedPayloads, candidateEncoding_reverse] using hn.2.1
  · exact eval_call_lifted TupleProgram.generateProgram p.register p.stack frame
      p.register_injective p.stack_injective ht

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
