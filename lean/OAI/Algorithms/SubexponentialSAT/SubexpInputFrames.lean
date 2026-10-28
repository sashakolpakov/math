import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Actual frame and tag readers for the row/input-pair stream. -/

namespace SubexponentialSAT.SubexpInputFrames

open BitProgram StructuredCalls

def ports {S : ℕ} (source target : Fin S) (h : source ≠ target) :
    RecordPrograms.Ports 8 S where
  tag := 0
  present := 1
  found := 2
  source := source
  payload := target
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := h

abbrev readField {S : ℕ} (source target : Fin S) (h : source ≠ target) : Cmd 8 S :=
  RecordPrograms.reader (ports source target h)

theorem readField_execute {S : ℕ} (source target : Fin S) (h : source ≠ target)
    (d : State 8 S) (bits tail : List Bool)
    (hsource : d.stacks source = Encoding.frame bits ++ tail)
    (hempty : d.stacks target = []) :
    ∃ e : State 8 S, Eval (readField source target h) (6 * bits.length + 4) d e ∧
      e.stacks = Function.update (Function.update d.stacks source tail) target bits.reverse := by
  let p := ports source target h
  let e := RecordPrograms.state p d false true (d.regs 2) tail bits.reverse
  have hstart : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) [] = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hsource hempty
  have ht := RecordPrograms.reader_eval p d bits tail [] (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hstart] at ht
  refine ⟨e, ?_, rfl⟩
  simpa only [List.append_nil] using ht

abbrev readTag {S : ℕ} (source : Fin S) : Cmd 8 S := .base (.atom (.pop source 7 6))

theorem readTag_execute {S : ℕ} (source : Fin S) (d : State 8 S)
    (bit : Bool) (tail : List Bool) (hsource : d.stacks source = bit :: tail) :
    ∃ e : State 8 S, Eval (readTag source) 1 d e ∧
      e.stacks = Function.update d.stacks source tail ∧ e.regs 7 = bit := by
  let e := (StructuredProgram.Atom.pop source 7 6).eval d
  refine ⟨e, .base (.atom _ _), ?_, ?_⟩
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hsource]
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hsource, readRegs]

end SubexponentialSAT.SubexpInputFrames

end OAI.Algorithms
