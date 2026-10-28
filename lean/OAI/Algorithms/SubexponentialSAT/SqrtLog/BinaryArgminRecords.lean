import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgminBootstrap
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-! A concrete paid loader for explicitly supplied binary-score records.
The representation stores the bits reversed inside each self-delimiting frame,
so the existing parser places each little-endian word directly on its stack.
The input supplies the scores; computing them is not part of this parser. -/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def recordEncoding : List Entry → List Bool
  | [] => []
  | a :: rest => true :: (Encoding.frame a.payload.reverse ++
      (Encoding.frame a.score.reverse ++ recordEncoding rest))

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

def scorePorts : RecordPrograms.Ports 8 9 where
  tag := 0
  present := 1
  found := 7
  source := 8
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev recordLoader : Cmd 8 9 :=
  .seq (atom (.pop 8 7 6))
    (.ite 7 (.seq (RecordPrograms.reader payloadPorts)
      (RecordPrograms.reader scorePorts)) (.base .skip))

private theorem read_eval (p : RecordPrograms.Ports 8 9) (d : Data)
    (bits tail : List Bool) (hs : d.stacks p.source = Encoding.frame bits ++ tail)
    (ho : d.stacks p.payload = []) :
    Eval (RecordPrograms.reader p) (6 * bits.length + 4) d
      (RecordPrograms.state p d false true (d.regs p.found) tail bits.reverse) := by
  have hi := RecordPrograms.state_eq_self p d (d.regs p.tag) (d.regs p.present)
    (d.regs p.found) (Encoding.frame bits ++ tail) [] rfl rfl rfl hs ho
  have h := RecordPrograms.reader_eval p d bits tail [] (d.regs p.tag)
    (d.regs p.present) (d.regs p.found)
  simpa only [hi, List.append_nil] using h

theorem recordLoader_nil (best : Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = false ∧
      Eval recordLoader 2 (data regs empty best (recordEncoding []))
        (data regs' empty best (recordEncoding [])) := by
  let d := data regs empty best (recordEncoding [])
  let a := (StructuredProgram.Atom.pop 8 7 6).eval d
  have hf : a.regs 7 = false := by
    simp [a, d, data, store, recordEncoding, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  have ha : a = data a.regs empty best (recordEncoding []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ d, data, store, recordEncoding, StructuredProgram.Atom.instr, execInstr]
  refine ⟨a.regs, hf, ?_⟩
  rw [← ha]
  exact Eval.seq (Eval.base (StructuredProgram.Eval.atom (.pop 8 7 6) d))
    (Eval.ite_false hf (Eval.base (.skip a)))

theorem recordLoader_cons (next best : Entry) (rest : List Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = true ∧
      Eval recordLoader (6 * next.payload.length + 6 * next.score.length + 10)
        (data regs empty best (recordEncoding (next :: rest)))
        (data regs' next best (recordEncoding rest)) := by
  let d := data regs empty best (recordEncoding (next :: rest))
  let a := (StructuredProgram.Atom.pop 8 7 6).eval d
  let tail := Encoding.frame next.score.reverse ++ recordEncoding rest
  have hat : a.regs 7 = true := by
    simp [a, d, data, store, recordEncoding, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  have has : a.stacks payloadPorts.source = Encoding.frame next.payload.reverse ++ tail := by
    simp [a, d, data, store, recordEncoding, payloadPorts, tail,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  have hao : a.stacks payloadPorts.payload = [] := by rfl
  have hp := read_eval payloadPorts a next.payload.reverse tail has hao
  let b := RecordPrograms.state payloadPorts a false true (a.regs 7) tail next.payload
  have hp' : Eval (RecordPrograms.reader payloadPorts)
      (6 * next.payload.length + 4) a b := by simpa [b, payloadPorts] using hp
  have hbs : b.stacks scorePorts.source = Encoding.frame next.score.reverse ++ recordEncoding rest := by
    simp [b, RecordPrograms.state, payloadPorts, scorePorts, tail]
  have hbo : b.stacks scorePorts.payload = [] := by rfl
  have hq := read_eval scorePorts b next.score.reverse (recordEncoding rest) hbs hbo
  let c := RecordPrograms.state scorePorts b false true (b.regs 7) (recordEncoding rest) next.score
  have hq' : Eval (RecordPrograms.reader scorePorts) (6 * next.score.length + 4) b c := by
    simpa [c, scorePorts] using hq
  have hct : c.regs 7 = true := by
    simp [c, b, RecordPrograms.state, payloadPorts, scorePorts, hat]
  have hc : c = data c.regs next best (recordEncoding rest) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [ b, a, d, RecordPrograms.state, payloadPorts, scorePorts,
        data, store, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  refine ⟨c.regs, hct, ?_⟩
  rw [← hc]
  convert Eval.seq (Eval.base (StructuredProgram.Eval.atom (.pop 8 7 6) d))
    (Eval.ite_true hat (Eval.seq hp' hq')) using 1 ; first | rfl | omega

theorem recordLoader_spec (B C : ℕ) :
    LoaderSpec recordLoader recordEncoding B C (6 * C + 6 * B + 10) where
  nil best regs _ := by
    obtain ⟨regs', hf, ht⟩ := recordLoader_nil best regs
    exact ⟨2, by omega, regs', hf, ht⟩
  cons next rest best regs _ hn _ := by
    obtain ⟨regs', hf, ht⟩ := recordLoader_cons next best rest regs
    exact ⟨_, by have hp := hn.2; rw [hn.1]; omega, regs', hf, ht⟩

theorem recordLoader_firstSpec (B C : ℕ) :
    FirstLoadSpec recordLoader recordEncoding B C (6 * C + 6 * B + 10) where
  nil regs := by
    obtain ⟨regs', hf, ht⟩ := recordLoader_nil empty regs
    exact ⟨2, by omega, regs', hf, ht⟩
  cons next rest regs hn _ := by
    obtain ⟨regs', hf, ht⟩ := recordLoader_cons next empty rest regs
    exact ⟨_, by have hp := hn.2; rw [hn.1]; omega, regs', hf, ht⟩

/-- The parser, initialization, all comparisons, all copies, and the terminal
load are included. Scores are supplied in binary and may be exponentially
large as numbers while the bound remains linear in their bit width. -/
theorem records_eval (B C : ℕ) (seed : Entry) (rest : List Entry)
    (regs : Fin 8 → Bool) (hs : Fits B C seed) (hr : ∀ a ∈ rest, Fits B C a) :
    ∃ n ≤ 120 * (B + C + 1) * (rest.length + 2), ∃ regs', regs' 7 = true ∧
      Eval (selectCommand recordLoader) n
        (data regs empty empty (recordEncoding (seed :: rest)))
        (data regs' empty (HashSelect.best value seed rest) []) := by
  obtain ⟨n, hn, regs', hf, ht⟩ := select_cons recordLoader recordEncoding B C
    (6 * C + 6 * B + 10) (recordLoader_spec B C) (recordLoader_firstSpec B C)
    seed rest regs hs hr
  refine ⟨n, ?_, regs', hf, ht⟩
  calc
    n ≤ (rest.length + 2) * (6 * C + 6 * B + 10 + 100 * (B + C + 1) + 3) :=
      hn.trans (select_cons_linear B C _ _)
    _ ≤ (rest.length + 2) * (120 * (B + C + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

def recordsProgram := compiled (selectCommand recordLoader) 8 2

theorem records_trace (B C : ℕ) (seed : Entry) (rest : List Entry)
    (regs : Fin 8 → Bool) (hs : Fits B C seed) (hr : ∀ a ∈ rest, Fits B C a) :
    ∃ n ≤ 120 * (B + C + 1) * (rest.length + 2) + 1, ∃ regs',
      Trace recordsProgram n
        ((data regs empty empty (recordEncoding (seed :: rest))).withPC
          (some recordsProgram.entry))
        ((data regs' empty (HashSelect.best value seed rest) []).withPC none) := by
  obtain ⟨n, hn, regs', _, ht⟩ := records_eval B C seed rest regs hs hr
  exact ⟨n + 1, Nat.add_le_add_right hn 1, regs', compiled_halt_trace ht 8 2⟩

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
