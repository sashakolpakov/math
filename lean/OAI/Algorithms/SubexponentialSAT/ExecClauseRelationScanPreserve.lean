import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan

namespace OAI.Algorithms

/-! A preserving wrapper for repeated clause-vs-formula scans. A real copy of
the full formula is scanned, and its residual copy is explicitly cleared. -/
namespace SubexponentialSAT.ExecClauseRelationScan.Preserving
open BitProgram StructuredCalls

abbrev Data := State 15 13

def stackPort (i : Fin 12) : Fin 13 := Fin.castAdd 1 i
def restrict (d : Data) : State 15 12 := ⟨d.regs, d.stacks ∘ stackPort⟩

theorem stackPort_injective : Function.Injective stackPort := Fin.castAdd_injective 12 1

private theorem embed_restrict (d : Data) :
    embedState id stackPort d (restrict d) = d := by
  cases d with
  | mk regs stk =>
    unfold embedState restrict
    congr 1
    · funext i
      exact Function.injective_id.extend_apply _ _ i
    · funext i
      by_cases h : ∃ j, stackPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact stackPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

def scanner (mode : Mode) := ProgramLinking.liftProgram
  (ExecClauseRelationScan.program mode) id stackPort

theorem scan_eval (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (hs : d.stacks 10 = encodeFormula F) (hp : d.stacks 11 = [])
    (hv : ExecClauseRelationScan.invariant Q (restrict d)) :
    ∃ n ≤ ExecClauseRelationScan.bound F Q, ∃ e : Data,
      Eval (.call (scanner mode)) n d e ∧
      ExecClauseRelationScan.invariant Q (restrict e) ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] ∧
      (e.stacks 10).length ≤ (encodeFormula F).length ∧
      e.stacks 12 = d.stacks 12 := by
  obtain ⟨n, hn, b, he, hb, hr, hout, hlen⟩ :=
    ExecClauseRelationScan.program_call mode F Q (restrict d) hs hp hv
  have ht : Trace (ExecClauseRelationScan.program mode) n
      ((restrict d).withPC (some (ExecClauseRelationScan.program mode).entry))
      (b.withPC none) := by
    cases he with
    | call _ h => exact h
  have heval := eval_call_lifted (ExecClauseRelationScan.program mode) id stackPort d
    Function.injective_id stackPort_injective ht
  rw [embed_restrict] at heval
  let e := embedState id stackPort d b
  have hstack (i : Fin 12) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stackPort_injective i
  have hreg (i : Fin 15) : e.regs i = b.regs i :=
    embedState_register _ _ _ _ Function.injective_id i
  have hre : restrict e = b := by
    cases b
    unfold restrict
    congr 1
    · funext i; exact hreg i
    · funext i; exact hstack i
  exact ⟨n, hn, e, heval, hre.symm ▸ hb, (hreg 14).trans hr,
    (hstack 11).trans hout, (congrArg List.length (hstack 10)).trans_le hlen,
    embedState_stack_frame _ _ _ _ _ (by decide)⟩

abbrev copyFormula : Cmd 15 13 := .call (StackRoutines.copyProgram 12 10 8 0 1)

def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 12 10 d.stacks⟩

theorem copyFormula_eval (d : Data) (htmp : d.stacks 8 = []) :
    Eval copyFormula (7 * (d.stacks 12).length + 5) d (copied d) := by
  have h := StackRoutines.copyProgram_trace (r := 15) (s := 13)
    12 10 8 0 1 (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

abbrev clearSource : Cmd 15 13 := .call (StackRoutines.clearProgram 10 0 1)

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 10 d.stacks⟩

theorem clearSource_eval (d : Data) :
    Eval clearSource (2 * (d.stacks 10).length + 3) d (cleared d) := by
  have h := StackRoutines.clearProgram_trace (r := 15) (s := 13) 10 0 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh

abbrev command (mode : Mode) : Cmd 15 13 :=
  .seq copyFormula (.seq (.call (scanner mode)) clearSource)

def invariant (F : Formula) (Q : Clause) (d : Data) : Prop :=
  d.stacks 12 = encodeFormula F ∧ ExecClauseRelationScan.invariant Q (restrict d) ∧
    d.stacks 10 = []

def bound (F : Formula) (Q : Clause) : ℕ :=
  512 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1)

/-- Both the original formula and query survive the scan. Only the output
singleton must be consumed before invoking another preserving scan. -/
theorem command_eval (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (valid : invariant F Q d) (hout : d.stacks 11 = []) :
    ∃ n, n + 1 ≤ bound F Q ∧ ∃ e : Data,
      Eval (command mode) n d e ∧ invariant F Q e ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] := by
  obtain ⟨hformula, hbase, hsource⟩ := valid
  have htmp : d.stacks 8 = [] := hbase.2 8
  have hs : (copied d).stacks 10 = encodeFormula F := by
    simp [copied, StackRoutines.copyStacks, hformula, hsource]
  have hp : (copied d).stacks 11 = [] := by
    simpa [copied, StackRoutines.copyStacks] using hout
  have hv : ExecClauseRelationScan.invariant Q (restrict (copied d)) := by
    refine ⟨?_, ?_⟩
    · simpa [restrict, stackPort, copied, StackRoutines.copyStacks] using hbase.1
    · intro i
      have hi10 : stackPort (Fin.castAdd 3 i) ≠ (10 : Fin 13) := by
        intro h
        have hv : i.val = 10 := congrArg Fin.val h
        omega
      simpa [restrict, copied, StackRoutines.copyStacks, hi10] using hbase.2 i
  obtain ⟨n, hn, e, he, hv, hr, hp, hlen, hf⟩ := scan_eval mode F Q (copied d) hs hp hv
  let result := cleared e
  let count := (7 * (d.stacks 12).length + 5) + (n + (2 * (e.stacks 10).length + 3))
  refine ⟨count, ?_, result, Eval.seq (copyFormula_eval d htmp) (Eval.seq he (clearSource_eval e)),
    ?_, ?_, ?_⟩
  · dsimp [count, bound]
    rw [hformula]
    dsimp [ExecClauseRelationScan.bound] at hn
    have hmargin :
        400 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) +
            9 * (encodeFormula F).length + 10 ≤
          512 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) := by
      nlinarith only [Nat.zero_le (encodeClause Q).length,
        Nat.zero_le (encodeFormula F).length]
    calc
      7 * (encodeFormula F).length + 5 + (n + (2 * (e.stacks 10).length + 3)) + 1 ≤
          400 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) +
            9 * (encodeFormula F).length + 10 := by omega
      _ ≤ 512 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) := hmargin
  · refine ⟨?_, ?_, ?_⟩
    · simpa [result, cleared, copied, StackRoutines.clearStacks,
        StackRoutines.copyStacks, hformula] using hf
    · refine ⟨?_, ?_⟩
      · simpa [restrict, stackPort, result, cleared, StackRoutines.clearStacks] using hv.1
      · intro i
        have hi10 : stackPort (Fin.castAdd 3 i) ≠ (10 : Fin 13) := by
          intro h
          have hv : i.val = 10 := congrArg Fin.val h
          omega
        simpa [restrict, result, cleared, StackRoutines.clearStacks, hi10] using hv.2 i
    · simp [result, cleared, StackRoutines.clearStacks]
  · simpa [result, cleared, readRegs] using hr
  · simpa [result, cleared, StackRoutines.clearStacks] using hp

def program (mode : Mode) := compiled (command mode) 12 11

theorem program_runsIn (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (valid : invariant F Q d) (hout : d.stacks 11 = []) :
    ∃ e : Data, RunsIn (program mode) (bound F Q)
      (d.withPC (some (program mode).entry)) (e.withPC none) ∧ invariant F Q e ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] := by
  obtain ⟨n, hn, e, he, hv, hr, hp⟩ := command_eval mode F Q d valid hout
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 12 11⟩, hv, hr, hp⟩

theorem primitive_execution (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (valid : invariant F Q d) (hout : d.stacks 11 = []) :
    ∃ e : Data, Computation.RunsIn (primitive (program mode)).step
      (primitiveOverhead (program mode) * bound F Q)
      (primitiveCfg (program mode) (d.withPC (some (program mode).entry)))
      (primitiveCfg (program mode) (e.withPC none)) ∧ invariant F Q e ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] := by
  obtain ⟨e, hr, hv, ha, hp⟩ := program_runsIn mode F Q d valid hout
  exact ⟨e, BitProgram.primitive_execution _ hr, hv, ha, hp⟩

end SubexponentialSAT.ExecClauseRelationScan.Preserving

end OAI.Algorithms
