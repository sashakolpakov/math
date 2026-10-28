import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SupportSelectionData
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRowPrepare
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! Fixed copying, comparison and record emission for support selection. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 64
abbrev Code := Cmd 16 64

def copy (src dst : Fin 64) : Code :=
  .call (StackRoutines.copyProgram src dst 42 (0 : Fin 16) 1)

def clear (src : Fin 64) : Code := .call (StackRoutines.clearProgram src (0 : Fin 16) 1)

def emitPorts (dst : Fin 64) (h : dst ≠ 34) : RecordPrograms.Ports 16 64 :=
  ⟨0, 1, 2, 34, dst, by decide, by decide, by decide, h.symm⟩

def emit (dst : Fin 64) (h : dst ≠ 34) : Code :=
  .seq (TupleProgram.pushConst dst 0 false)
    (.seq (TupleProgram.escape (emitPorts dst h)) (TupleProgram.pushConst dst 0 true))

theorem emit_eval (dst : Fin 64) (h : dst ≠ 34) (d : Data) (v : ℕ)
    (hv : d.stacks 34 = unary v) :
    ∃ e, Eval (emit dst h) (5 * v + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks 34 []) dst
        (record v ++ d.stacks dst) := by
  let a := TupleProgram.pushedState dst 0 false d
  let b := TupleProgram.escapedState (emitPorts dst h) a
  let e := TupleProgram.pushedState dst 0 true b
  have h1 := TupleProgram.pushConst_eval dst 0 false d
  have h2 := TupleProgram.escape_eval_state (emitPorts dst h) a
  have h3 := TupleProgram.pushConst_eval dst 0 true b
  refine ⟨e, ?_, ?_⟩
  · have he := h1.seq (h2.seq h3)
    change Eval (emit dst h) _ d e at he
    convert he using 1
    simp [a, emitPorts, h.symm, hv] ; omega
  · funext j
    by_cases hj : j = dst
    · subst j
      simp [e, b, a,
        emitPorts, h.symm, hv, record, TupleProgram.frame_eq_escaped, List.append_assoc]
    · by_cases hk : j = 34
      · subst j
        simp [e, b, a,
          emitPorts, h.symm]
      · simp [e, b, a,
          emitPorts, hj, hk]

def compareRegs : Fin 5 → Fin 16 := Fin.castAdd 11
def comparePorts : Fin 2 → Fin 64 := ![4, 7]

theorem compareRegs_injective : Function.Injective compareRegs := Fin.castAdd_injective 5 11
theorem comparePorts_injective : Function.Injective comparePorts := by decide

def compareColors : Code := .call
  (ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram compareRegs comparePorts)

theorem compareColors_eval (d : Data) :
    ∃ n e left right, n ≤ 9 * ((d.stacks 4).length + 1) ∧
      Eval compareColors n d e ∧
      e.stacks = Function.update (Function.update d.stacks 4 left) 7 right ∧
      e.regs 4 = decide (d.stacks 4 = d.stacks 7) ∧
      left.length ≤ (d.stacks 4).length ∧ right.length ≤ (d.stacks 7).length := by
  obtain ⟨c, ⟨n, hn, ht⟩, hc, hout, hl, hr⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded (d.regs ∘ compareRegs) (d.stacks 4) (d.stacks 7)
  let a := projectState compareRegs comparePorts d
  let b : State 5 2 := ⟨c.regs, c.stacks⟩
  let e := embedState compareRegs comparePorts d b
  have hb : b.withPC none = c := by
    cases c
    simp_all [b, StructuredProgram.State.withPC]
  have ha : a.withPC (some ExecClauseCost.bitEqualityProgram.entry) =
      ExecClauseCost.bitEqualityStart (d.regs ∘ compareRegs) (d.stacks 4) (d.stacks 7) := by
    apply congrArg (fun st : Fin 2 → List Bool =>
      (⟨some 0, d.regs ∘ compareRegs, st⟩ : Cfg 5 2 10))
    funext i
    fin_cases i <;> rfl
  have hrun : Trace ExecClauseCost.bitEqualityProgram n
      (a.withPC (some ExecClauseCost.bitEqualityProgram.entry)) (b.withPC none) := by
    rw [ha, hb]
    exact ht
  refine ⟨n, e, c.stacks 0, c.stacks 1, hn,
    eval_call_from_state _ _ _ _ compareRegs_injective comparePorts_injective hrun,
    ?_, ?_, hl, hr⟩
  · have hbs : b.stacks = Function.update (Function.update a.stacks 0 (c.stacks 0))
        1 (c.stacks 1) := by
      funext i
      fin_cases i <;> simp [b]
    change Function.extend comparePorts b.stacks d.stacks = _
    rw [hbs, ProgramLinking.extend_update comparePorts_injective,
      ProgramLinking.extend_update comparePorts_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project compareRegs comparePorts d compareRegs_injective comparePorts_injective)
    change Function.extend comparePorts a.stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl
  · change (embedState compareRegs comparePorts d b).regs (compareRegs 4) = _
    rw [embedState_register _ _ _ _ compareRegs_injective]
    exact hout

def selectColor : Code := .ite 4 (emit 0 (by decide)) (.base .skip)

theorem selectColor_eval (d : Data) (v : ℕ) (hv : d.stacks 34 = unary v) :
    ∃ n e, n ≤ 5 * v + 8 ∧ Eval selectColor n d e ∧
      e.stacks = Function.update (Function.update d.stacks 34
        (if d.regs 4 then [] else d.stacks 34)) 0
        (if d.regs 4 then record v ++ d.stacks 0 else d.stacks 0) := by
  cases hh : d.regs 4 with
  | false =>
    refine ⟨1, d, by omega, .ite_false hh (.base (.skip d)), ?_⟩
    simp []
  | true =>
    obtain ⟨e, he, hs⟩ := emit_eval 0 (by decide) d v hv
    exact ⟨5 * v + 8, e, le_rfl, by simpa [selectColor, Nat.add_assoc] using Eval.ite_true hh he,
      by simpa [hh] using hs⟩

def cleanupPorts : List (Fin 64) := [3, 4, 5, 7, 34, 36]
def cleanup : Code := GlobalBasisProgram.clearList cleanupPorts

theorem cleanup_eval (d : Data) (bound : ℕ)
    (hb : ∀ j ∈ cleanupPorts, (d.stacks j).length ≤ bound) :
    ∃ n ≤ cleanupPorts.length * (2 * bound + 3), ∃ e : Data,
      Eval cleanup n d e ∧
      (∀ j, e.stacks j = if j ∈ cleanupPorts then [] else d.stacks j) := by
  obtain ⟨n, e, hn, he, hs⟩ := GlobalBasisProgram.clearList_eval cleanupPorts d
  refine ⟨n, ?_, e, he, fun j => congrFun hs j⟩
  have h3 := hb 3 (by decide)
  have h4 := hb 4 (by decide)
  have h5 := hb 5 (by decide)
  have h7 := hb 7 (by decide)
  have h34 := hb 34 (by decide)
  have h36 := hb 36 (by decide)
  simp only [cleanupPorts, GlobalBasisProgram.clearBudget] at hn
  norm_num [cleanupPorts]
  omega

def Clean (d : Data) : Prop :=
  ∀ j ∈ ([3,4,5,7,16,17,18,19,20,21,22,34,36,40,41,42] : List (Fin 64)), d.stacks j = []

theorem Clean.cleanup (d : Data) (h : Clean d) (j : Fin 64) (hj : j ∈ cleanupPorts) :
    d.stacks j = [] := by
  apply h j
  simp only [cleanupPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The only ports changed by a vertex visit before cleanup. -/
def CoreFrame (d e : Data) : Prop :=
  ∀ j, j ≠ 0 → j ≠ 1 → j ∉ cleanupPorts → e.stacks j = d.stacks j

def prefixBound (L v t r g : ℕ) : ℕ :=
  400 * (L + v + 1)^2 + SubexpHeadColorProgram.budget t r + 7*g + 12*v + 9*r + 60

def visitBound (L v t r g : ℕ) : ℕ := 13 * prefixBound L v t r g + 30

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
