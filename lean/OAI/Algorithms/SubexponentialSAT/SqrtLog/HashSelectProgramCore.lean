import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgminScan
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-! Fixed-port binary argmin calls and a parser for unevaluated candidate
payloads. The scores are absent from the input encoding. All supplied commands
are actual finite programs; semantic scores are never atomic instructions. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Entry := BinaryArgmin.Entry

structure Ports (r s : ℕ) where
  register : Fin 8 → Fin r
  stack : Fin 9 → Fin s
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

noncomputable def state {r s : ℕ} (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) : State r s :=
  embedState p.register p.stack frame (BinaryArgmin.data regs next best queue)

@[simp] theorem state_register {r s : ℕ} (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) (i : Fin 8) :
    (state p frame regs next best queue).regs (p.register i) = regs i :=
  embedState_register _ _ _ _ p.register_injective i

@[simp] theorem state_stack {r s : ℕ} (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) (i : Fin 9) :
    (state p frame regs next best queue).stacks (p.stack i) =
      BinaryArgmin.store next best queue i :=
  embedState_stack _ _ _ _ p.stack_injective i

def updateProgram := compiled BinaryArgmin.update 8 2

abbrev update {r s : ℕ} (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram updateProgram p.register p.stack)

theorem update_eval {r s : ℕ} (p : Ports r s) (frame : State r s)
    (B C : ℕ) (next best : Entry) (queue : List Bool) (regs : Fin 8 → Bool)
    (hn : BinaryArgmin.Fits B C next) (hb : BinaryArgmin.Fits B C best) :
    ∃ n ≤ 100 * (B + C + 1) + 1, ∃ regs',
      Eval (update p) n (state p frame regs next best queue)
        (state p frame regs' BinaryArgmin.empty (BinaryArgmin.pick best next) queue) := by
  obtain ⟨n, hn', regs', ht⟩ := BinaryArgmin.update_eval B C next best queue regs
    hn.1 hb.1 hn.2 hb.2
  exact ⟨n + 1, Nat.add_le_add_right hn' 1, regs',
    eval_call_lifted updateProgram p.register p.stack frame
      p.register_injective p.stack_injective (compiled_halt_trace ht 8 2)⟩

/-- Only payloads are serialized. In particular no uncomputed score is supplied
as input data to this parser. A final false list marker is consumed. -/
def candidateEncoding : List (List Bool) → List Bool
  | [] => [false]
  | a :: rest => true :: (Encoding.frame a.reverse ++ candidateEncoding rest)

def payloadPorts : RecordPrograms.Ports 8 9 where
  tag := 0
  present := 1
  found := 7
  source := 8
  payload := 0
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev parserCmd : Cmd 8 9 :=
  .seq (BinaryArgmin.atom (.pop 8 7 6))
    (.ite 7 (RecordPrograms.reader payloadPorts) (.base .skip))

def parserProgram := compiled parserCmd 8 0

abbrev parse {r s : ℕ} (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram parserProgram p.register p.stack)

private theorem parser_nil (best : Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = false ∧
      Eval parserCmd 2 (BinaryArgmin.data regs BinaryArgmin.empty best [false])
        (BinaryArgmin.data regs' BinaryArgmin.empty best []) := by
  let d := BinaryArgmin.data regs BinaryArgmin.empty best [false]
  let a := (StructuredProgram.Atom.pop 8 7 6).eval d
  have hf : a.regs 7 = false := by
    simp [a, d, BinaryArgmin.data, BinaryArgmin.store, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  have ha : a = BinaryArgmin.data a.regs BinaryArgmin.empty best [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ d, BinaryArgmin.data, BinaryArgmin.store, StructuredProgram.Atom.instr, execInstr]
  refine ⟨a.regs, hf, ?_⟩
  rw [← ha]
  exact Eval.seq (Eval.base (StructuredProgram.Eval.atom (.pop 8 7 6) d))
    (Eval.ite_false hf (Eval.base (.skip a)))

private theorem parser_cons (bits : List Bool) (rest : List (List Bool))
    (best : Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = true ∧
      Eval parserCmd (6 * bits.length + 6)
        (BinaryArgmin.data regs BinaryArgmin.empty best (candidateEncoding (bits :: rest)))
        (BinaryArgmin.data regs' ⟨bits, []⟩ best (candidateEncoding rest)) := by
  let d := BinaryArgmin.data regs BinaryArgmin.empty best (candidateEncoding (bits :: rest))
  let a := (StructuredProgram.Atom.pop 8 7 6).eval d
  have ht : a.regs 7 = true := by
    simp [a, d, BinaryArgmin.data, BinaryArgmin.store, candidateEncoding,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs]
  have hs : a.stacks payloadPorts.source =
      Encoding.frame bits.reverse ++ candidateEncoding rest := by
    simp [a, d, BinaryArgmin.data, BinaryArgmin.store, candidateEncoding, payloadPorts,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  have ho : a.stacks payloadPorts.payload = [] := rfl
  have hi := RecordPrograms.state_eq_self payloadPorts a (a.regs 0) (a.regs 1)
    (a.regs 7) _ [] rfl rfl rfl hs ho
  have hr := RecordPrograms.reader_eval payloadPorts a bits.reverse
    (candidateEncoding rest) [] (a.regs 0) (a.regs 1) (a.regs 7)
  rw [hi] at hr
  let b := RecordPrograms.state payloadPorts a false true (a.regs 7)
    (candidateEncoding rest) bits
  have hr' : Eval (RecordPrograms.reader payloadPorts) (6 * bits.length + 4) a b := by
    simpa [b] using hr
  have hb : b = BinaryArgmin.data b.regs ⟨bits, []⟩ best (candidateEncoding rest) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ a, d, payloadPorts,
        BinaryArgmin.data, BinaryArgmin.store, BinaryArgmin.empty,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  refine ⟨b.regs, ?_, ?_⟩
  · simpa [b, payloadPorts, RecordPrograms.state] using ht
  · rw [← hb]
    convert Eval.seq (Eval.base (StructuredProgram.Eval.atom (.pop 8 7 6) d))
      (Eval.ite_true ht hr') using 1 ; first | rfl | omega

theorem parse_nil {r s : ℕ} (p : Ports r s) (frame : State r s)
    (best : Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = false ∧
      Eval (parse p) 3 (state p frame regs BinaryArgmin.empty best [false])
        (state p frame regs' BinaryArgmin.empty best []) := by
  obtain ⟨regs', hf, ht⟩ := parser_nil best regs
  exact ⟨regs', hf, eval_call_lifted parserProgram p.register p.stack frame
    p.register_injective p.stack_injective (compiled_halt_trace ht 8 0)⟩

theorem parse_cons {r s : ℕ} (p : Ports r s) (frame : State r s)
    (bits : List Bool) (rest : List (List Bool)) (best : Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = true ∧
      Eval (parse p) (6 * bits.length + 7)
        (state p frame regs BinaryArgmin.empty best (candidateEncoding (bits :: rest)))
        (state p frame regs' ⟨bits, []⟩ best (candidateEncoding rest)) := by
  obtain ⟨regs', ht, he⟩ := parser_cons bits rest best regs
  refine ⟨regs', ht, ?_⟩
  convert eval_call_lifted parserProgram p.register p.stack frame
    p.register_injective p.stack_injective (compiled_halt_trace he 8 0) using 1 <;>
    first | rfl

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
