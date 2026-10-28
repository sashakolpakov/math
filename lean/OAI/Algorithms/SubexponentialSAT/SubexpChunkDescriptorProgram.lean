import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.ChunkPartition

namespace OAI.Algorithms

/-!
# A finite chunk-descriptor producer

The core consumes a unary variable count on stack 0 and preserves a positive
unary chunk width on stack 1. Its two output streams are the framed unary
widths and the framed singleton scopes, in increasing chunk order. All loops
below inspect actual stack bits/presence flags. Natural-number functions in
the specifications do not occur in instructions.
-/

namespace SubexponentialSAT.SubexpChunkDescriptorProgram

open BitProgram StructuredProgram StructuredCalls

abbrev Data := StructuredProgram.State 3 10
abbrev Regs := Fin 3 → Bool

def work (regs : Regs) (remaining width counter index widths scopes : List Bool) : Data :=
  ⟨regs, ![remaining, width, counter, [], index, widths, scopes, [], [], []]⟩

abbrev emit (dst : Fin 10) (b : Bool) : StructuredCalls.Cmd 3 10 :=
  .base (.seq (.atom (.set 2 b)) (.atom (.push dst 2)))

def emitted (dst : Fin 10) (b : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 2 b, Function.update d.stacks dst (b :: d.stacks dst)⟩

theorem emit_eval (dst : Fin 10) (b : Bool) (d : Data) :
    StructuredCalls.Eval (emit dst b) 2 d (emitted dst b d) := by
  have h := (StructuredProgram.Eval.atom (.set (2 : Fin 3) b) d).seq
    (StructuredProgram.Eval.atom (.push dst 2) _)
  exact .base (by simpa [emitted, Atom.eval, Atom.instr, State.ofCfg, State.withPC,
    execInstr] using h)

/-- This list is part of the finite program text, never runtime data. -/
def emitBits (dst : Fin 10) : List Bool → StructuredCalls.Cmd 3 10
  | [] => .base .skip
  | b :: bs => .seq (emit dst b) (emitBits dst bs)

def emittedBits (dst : Fin 10) (bits : List Bool) (d : Data) : Data :=
  bits.foldl (fun a b => emitted dst b a) d

theorem emitBits_eval (dst : Fin 10) (bits : List Bool) (d : Data) :
    StructuredCalls.Eval (emitBits dst bits) (2 * bits.length) d
      (emittedBits dst bits d) := by
  induction bits generalizing d with
  | nil => exact .base (.skip d)
  | cons b bs ih =>
      simpa [emitBits, emittedBits, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using (emit_eval dst b d).seq (ih (emitted dst b d))

theorem emittedBits_stacks (dst : Fin 10) (bits : List Bool) (d : Data) :
    (emittedBits dst bits d).stacks =
      Function.update d.stacks dst (bits.reverse ++ d.stacks dst) := by
  induction bits generalizing d with
  | nil => simp [emittedBits]
  | cons b bs ih =>
      simp only [emittedBits, List.foldl_cons]
      rw [show (List.foldl (fun a b => emitted dst b a) (emitted dst b d) bs).stacks =
        Function.update (emitted dst b d).stacks dst
          (bs.reverse ++ (emitted dst b d).stacks dst) from ih _]
      simp [emitted, List.reverse_cons, List.append_assoc]

theorem emitBits_work5 (bits : List Bool) (regs : Regs)
    (remaining width counter index widths scopes : List Bool) :
    ∃ regs', StructuredCalls.Eval (emitBits 5 bits) (2 * bits.length)
      (work regs remaining width counter index widths scopes)
      (work regs' remaining width counter index (bits.reverse ++ widths) scopes) := by
  let d := work regs remaining width counter index widths scopes
  refine ⟨(emittedBits 5 bits d).regs, ?_⟩
  have he := emitBits_eval 5 bits d
  convert he using 1
  apply CounterForPrograms.data_ext
  · rfl
  · rw [emittedBits_stacks]
    funext i
    fin_cases i <;> simp [work, d]

theorem emitBits_work6 (bits : List Bool) (regs : Regs)
    (remaining width counter index widths scopes : List Bool) :
    ∃ regs', StructuredCalls.Eval (emitBits 6 bits) (2 * bits.length)
      (work regs remaining width counter index widths scopes)
      (work regs' remaining width counter index widths (bits.reverse ++ scopes)) := by
  let d := work regs remaining width counter index widths scopes
  refine ⟨(emittedBits 6 bits d).regs, ?_⟩
  have he := emitBits_eval 6 bits d
  convert he using 1
  apply CounterForPrograms.data_ext
  · rfl
  · rw [emittedBits_stacks]
    funext i
    fin_cases i <;> simp [work, d]

def counterPorts : UnaryForPrograms.Ports 3 10 := ⟨2, 0, 1⟩

theorem popped_work (regs : Regs) (remaining width counter index widths scopes : List Bool) :
    UnaryForPrograms.popped counterPorts (work regs remaining width counter index widths scopes) =
      work (readRegs regs 0 1 counter.head?) remaining width counter.tail index widths scopes := by
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [UnaryForPrograms.popped, counterPorts, work]

abbrev popRemaining : StructuredCalls.Cmd 3 10 := .base (.atom (.pop 0 0 1))

theorem popRemaining_eval (regs : Regs)
    (remaining width counter index widths scopes : List Bool) :
    StructuredCalls.Eval popRemaining 1 (work regs remaining width counter index widths scopes)
      (work (readRegs regs 0 1 remaining.head?) remaining.tail width counter index widths scopes) := by
  have h := StructuredProgram.Eval.atom (.pop (0 : Fin 10) (0 : Fin 3) 1)
    (work regs remaining width counter index widths scopes)
  apply StructuredCalls.Eval.base
  convert h using 1
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, work]

abbrev takeOne : StructuredCalls.Cmd 3 10 :=
  .seq popRemaining (.ite 1 (emitBits 5 [true, true]) (.base .skip))

theorem takeOne_nil (regs : Regs) (width counter index widths scopes : List Bool) :
    ∃ regs', StructuredCalls.Eval takeOne 2 (work regs [] width counter index widths scopes)
      (work regs' [] width counter index widths scopes) := by
  let regs' := readRegs regs 0 1 none
  refine ⟨regs', ?_⟩
  have hb : (work regs' [] width counter index widths scopes).regs 1 = false := by
    simp [regs', work, readRegs]
  exact (popRemaining_eval regs [] width counter index widths scopes).seq
    (.ite_false hb (.base (.skip _)))

theorem takeOne_cons (regs : Regs) (b : Bool)
    (remaining width counter index widths scopes : List Bool) :
    ∃ regs', StructuredCalls.Eval takeOne 6
      (work regs (b :: remaining) width counter index widths scopes)
      (work regs' remaining width counter index (true :: true :: widths) scopes) := by
  let regs' := readRegs regs 0 1 (some b)
  obtain ⟨regs'', he⟩ := emitBits_work5 [true, true] regs' remaining width counter index widths scopes
  refine ⟨regs'', ?_⟩
  have hb : (work regs' remaining width counter index widths scopes).regs 1 = true := by
    simp [regs', work, readRegs]
  exact (popRemaining_eval regs (b :: remaining) width counter index widths scopes).seq
    (.ite_true hb he)

abbrev takeChunk : StructuredCalls.Cmd 3 10 := UnaryForPrograms.forCmd counterPorts takeOne

theorem takeChunk_visits (counter : List Bool) :
    ∀ (regs : Regs) (remaining width index widths scopes : List Bool),
      ∃ costs n regs', UnaryForPrograms.Visits counterPorts takeOne costs n
        (work regs remaining width counter index widths scopes)
        (work regs' (remaining.drop counter.length) width [] index
          (List.replicate (2 * min counter.length remaining.length) true ++ widths) scopes) ∧
        n ≤ 8 * counter.length + 2 := by
  induction counter with
  | nil =>
      intro regs remaining width index widths scopes
      refine ⟨[], 2, readRegs regs 0 1 none, ?_, by simp⟩
      simpa [popped_work] using
        (UnaryForPrograms.Visits.done (p := counterPorts) (body := takeOne)
          (work regs remaining width [] index widths scopes) rfl)
  | cons bit counter ih =>
      intro regs remaining width index widths scopes
      let r₁ := readRegs regs 0 1 (some bit)
      cases remaining with
      | nil =>
          obtain ⟨r₂, hb⟩ := takeOne_nil r₁ width counter index widths scopes
          obtain ⟨costs, n, r₃, ht, hn⟩ := ih r₂ [] width index widths scopes
          refine ⟨2 :: costs, 2 + n + 2, r₃, ?_, by simp only [List.length_cons]; omega⟩
          have hv := UnaryForPrograms.Visits.step
            (p := counterPorts) (body := takeOne)
            (d := work regs [] width (bit :: counter) index widths scopes)
            (by simp [work, counterPorts]) (by simpa [popped_work, r₁] using hb)
            (by simp [UnaryForPrograms.popped, work, counterPorts]) ht
          simpa using hv
      | cons b remaining =>
          obtain ⟨r₂, hb⟩ := takeOne_cons r₁ b remaining width counter index widths scopes
          obtain ⟨costs, n, r₃, ht, hn⟩ := ih r₂ remaining width index
            (true :: true :: widths) scopes
          refine ⟨6 :: costs, 6 + n + 2, r₃, ?_, by simp only [List.length_cons]; omega⟩
          have hv := UnaryForPrograms.Visits.step
            (p := counterPorts) (body := takeOne)
            (d := work regs (b :: remaining) width (bit :: counter) index widths scopes)
            (by simp [work, counterPorts]) (by simpa [popped_work, r₁] using hb)
            (by simp [UnaryForPrograms.popped, work, counterPorts]) ht
          simpa [List.drop_succ_cons, Nat.mul_add, List.replicate_add, List.append_assoc] using hv

theorem takeChunk_eval (regs : Regs) (remaining width counter index widths scopes : List Bool) :
    ∃ n regs', StructuredCalls.Eval takeChunk n
      (work regs remaining width counter index widths scopes)
      (work regs' (remaining.drop counter.length) width [] index
        (List.replicate (2 * min counter.length remaining.length) true ++ widths) scopes) ∧
      n ≤ 8 * counter.length + 2 := by
  obtain ⟨costs, n, regs', hv, hn⟩ := takeChunk_visits counter regs remaining width index widths scopes
  exact ⟨n, regs', hv.eval, hn⟩

end SubexponentialSAT.SubexpChunkDescriptorProgram

end OAI.Algorithms
