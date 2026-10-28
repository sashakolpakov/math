import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-!
# Physical high-incidence selection from supplied explicit scopes

The input is a framed list of scopes with original natural-number identifiers.
Every query invokes the audited source-preserving record/membership scan. The
cutoff is a supplied unary integer in this module; no arithmetic or translation
from clauses to scopes is silently performed. The fixed program appends the
strict comparison bit and advances the original-coordinate counter.
-/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 10 16
abbrev Code := Cmd 10 16
abbrev unary (n : ℕ) := List.replicate n true
abbrev scopeBits := SubexpIncidenceSlotProgram.scopeBits
abbrev degree := Subexp.IncidencePlanSpec.degree

def state (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (v cut : ℕ) (mask fuel : List Bool) : Data :=
  ⟨regs, ![scopeBits scopes, unary scopes.length, unary v, [], [], [], [], [],
    [], [], [], [], [], unary (cut + 1), mask, fuel]⟩

def countPorts : Fin 13 → Fin 16 := Fin.castAdd 3

theorem countPorts_injective : Function.Injective countPorts := Fin.castAdd_injective _ _

def count : Code := .call (ProgramLinking.liftProgram
  SubexpIncidenceSlotProgram.program id countPorts)

theorem count_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (v cut : ℕ) (mask fuel : List Bool) :
    ∃ n rf, n ≤ SubexpIncidenceSlotProgram.budget scopes scopes.length v ∧
      Eval count n (state regs scopes v cut mask fuel)
        ⟨rf, Function.update (state regs scopes v cut mask fuel).stacks 3
          (unary (degree scopes v + 1))⟩ := by
  let a := state regs scopes v cut mask fuel
  have hp : projectState id countPorts a =
      SubexpIncidenceSlotProgram.idle regs scopes scopes.length v [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨rf, n, hn, ht⟩ := SubexpIncidenceSlotProgram.program_run regs scopes
    scopes.length v le_rfl
  have hd : SubexpIncidenceSlotProgram.degree scopes scopes.length v = degree scopes v := by
    simp [SubexpIncidenceSlotProgram.degree, degree,
      Subexp.IncidencePlanSpec.degree, Subexp.IncidencePlanSpec.incidentIndices]
  let b := SubexpIncidenceSlotProgram.idle rf scopes scopes.length v
    (unary (degree scopes v + 1))
  rw [hd] at ht
  rw [← hp] at ht
  have he := eval_call_from_state SubexpIncidenceSlotProgram.program id countPorts a
    Function.injective_id countPorts_injective ht
  have hb : embedState id countPorts a b =
      (⟨rf, Function.update a.stacks 3 (unary (degree scopes v + 1))⟩ : Data) := by
    apply embedState_eq_of_ports id countPorts a _ b
      Function.injective_id countPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
      simp [h3]
  change Eval count n a (embedState id countPorts a b) at he
  rw [hb] at he
  exact ⟨n, rf, hn, he⟩

def copy (src dst tmp : Fin 16) : Code :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)
def copied (src dst : Fin 16) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩
theorem copy_eval (src dst tmp : Fin 16) (a : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (ht : a.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (a.stacks src).length + 5) a (copied src dst a) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide)
    a.regs a.stacks ht)

def compareRegs : Fin 4 → Fin 10 := Fin.castAdd 6
def comparePorts : Fin 2 → Fin 16 := ![3, 4]
theorem compareRegs_injective : Function.Injective compareRegs := Fin.castAdd_injective _ _
theorem comparePorts_injective : Function.Injective comparePorts := by decide

def compare : Code := .call (ProgramLinking.liftProgram
  Subexp.UnaryCompare.program compareRegs comparePorts)

theorem compare_eval (a : Data) :
    ∃ n b, Eval compare n a b ∧
      n ≤ 4 * min (a.stacks 3).length (a.stacks 4).length + 6 ∧
      b.regs 3 = decide ((a.stacks 3).length ≤ (a.stacks 4).length) ∧
      (b.stacks 3).length ≤ (a.stacks 3).length ∧
      (b.stacks 4).length ≤ (a.stacks 4).length ∧
      (∀ i : Fin 16, i ≠ 3 → i ≠ 4 → b.stacks i = a.stacks i) := by
  obtain ⟨n, hn, c, ht, hpc, hf⟩ := Subexp.UnaryCompare.runs
    (a.regs ∘ compareRegs) (a.stacks 3) (a.stacks 4)
  let d : State 4 2 := ⟨c.regs, c.stacks⟩
  have hc : d.withPC none = c := by cases c; simp_all [d, StructuredProgram.State.withPC]
  have hp : Subexp.UnaryCompare.start (a.regs ∘ compareRegs) (a.stacks 3) (a.stacks 4) =
      (projectState compareRegs comparePorts a).withPC
        (some Subexp.UnaryCompare.program.entry) := by
    change Cfg.mk _ _ _ = Cfg.mk _ _ _
    congr 1
    funext i; fin_cases i <;> rfl
  rw [hp, ← hc] at ht
  let b := embedState compareRegs comparePorts a d
  have he := eval_call_from_state Subexp.UnaryCompare.program compareRegs comparePorts a
    compareRegs_injective comparePorts_injective ht
  have hs (i : Fin 2) : b.stacks (comparePorts i) = c.stacks i :=
    embedState_stack _ _ _ _ comparePorts_injective i
  refine ⟨n, b, he, hn, ?_, ?_, ?_, ?_⟩
  · exact (embedState_register _ _ _ _ compareRegs_injective 3).trans hf
  · have hl := Subexp.UnaryCompare.trace_length_le ht 0
    change (c.stacks 0).length ≤ (a.stacks 3).length at hl
    have hs0 := hs 0
    change b.stacks 3 = c.stacks 0 at hs0
    simpa only [← hs0] using hl
  · have hl := Subexp.UnaryCompare.trace_length_le ht 1
    change (c.stacks 1).length ≤ (a.stacks 4).length at hl
    have hs1 := hs 1
    change b.stacks 4 = c.stacks 1 at hs1
    simpa only [← hs1] using hl
  · intro i h3 h4
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [comparePorts] at hj <;> simp_all

def pushTrue (dst : Fin 16) : Code :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push dst 0)))
def pushedTrue (dst : Fin 16) (a : Data) : Data :=
  ⟨Function.update a.regs 0 true, Function.update a.stacks dst (true :: a.stacks dst)⟩
theorem pushTrue_eval (dst : Fin 16) (a : Data) :
    Eval (pushTrue dst) 2 a (pushedTrue dst a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) true) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 10)) _))
  simpa [pushTrue, pushedTrue, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def emitHigh : Code := .seq (.base (.atom (.bnot 3 3))) (.base (.atom (.push 14 3)))
def emittedHigh (a : Data) : Data :=
  ⟨Function.update a.regs 3 (!a.regs 3), Function.update a.stacks 14 ((!a.regs 3) :: a.stacks 14)⟩
theorem emitHigh_eval (a : Data) : Eval emitHigh 2 a (emittedHigh a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.bnot (3 : Fin 10) 3) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (14 : Fin 16) (3 : Fin 10)) _))
  simpa [emitHigh, emittedHigh, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def query : Code := .seq count (.seq (copy 13 4 8)
  (.seq compare (.seq emitHigh (.seq (WorkspaceCleanupProgram.command 0 1 [3, 4]) (pushTrue 2)))))

def queryBudget (scopes : List (List ℕ)) (v cut : ℕ) : ℕ :=
  SubexpIncidenceSlotProgram.budget scopes scopes.length v +
    20 * (cut + degree scopes v + 2) + 20

theorem query_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (v cut : ℕ) (mask fuel : List Bool) :
    ∃ n rf, n ≤ queryBudget scopes v cut ∧
      Eval query n (state regs scopes v cut mask fuel)
        (state rf scopes (v + 1) cut (decide (cut < degree scopes v) :: mask) fuel) := by
  let a := state regs scopes v cut mask fuel
  obtain ⟨nc, rc, hnc, hec⟩ := count_eval regs scopes v cut mask fuel
  let b : Data := ⟨rc, Function.update a.stacks 3 (unary (degree scopes v + 1))⟩
  let c := copied 13 4 b
  have hecopy := copy_eval 13 4 8 b (by decide) (by decide) (by decide) (by rfl)
  obtain ⟨nt, d, het, hnt, hflag, h3, h4, hframe⟩ := compare_eval c
  have hc3 : c.stacks 3 = unary (degree scopes v + 1) := by
    simp [c, copied, StackRoutines.copyStacks, b]
  have hc4 : c.stacks 4 = unary (cut + 1) := by
    simp [c, copied, StackRoutines.copyStacks, b, a, state]
  have hcframe (i : Fin 16) (hi3 : i ≠ 3) (hi4 : i ≠ 4) : c.stacks i = a.stacks i := by
    simp [c, copied, StackRoutines.copyStacks, b, hi3, hi4]
  have hhigh : (!d.regs 3) = decide (cut < degree scopes v) := by
    rw [hflag, hc3, hc4]
    simp only [unary, List.length_replicate, ← decide_not]
    simp only [Nat.not_le, Nat.add_lt_add_iff_right]
  let e := emittedHigh d
  let f := WorkspaceCleanupProgram.finish 0 1 [3, 4] e
  let g := pushedTrue 2 f
  have hclean := WorkspaceCleanupProgram.command_eval (0 : Fin 10) 1
    ([3, 4] : List (Fin 16)) (by decide) e
  have hg : g = state g.regs scopes (v + 1) cut
      (decide (cut < degree scopes v) :: mask) fuel := by
    apply congrArg (StructuredProgram.State.mk g.regs)
    funext i
    have hf3 : f.stacks 3 = [] := by simp [f]
    have hf4 : f.stacks 4 = [] := by simp [f]
    have hdframe (j : Fin 16) (hj3 : j ≠ 3) (hj4 : j ≠ 4) :=
      (hframe j hj3 hj4).trans (hcframe j hj3 hj4)
    fin_cases i <;>
      simp [ f, e, emittedHigh, hhigh, hdframe,
        a, state, List.replicate_succ]
  have he := hec.seq (hecopy.seq (het.seq ((emitHigh_eval d).seq
    (hclean.seq (pushTrue_eval 2 f)))))
  change Eval query _ a g at he
  rw [hg] at he
  refine ⟨_, g.regs, ?_, he⟩
  have hcopylen : (b.stacks 13).length = cut + 1 := by simp [b, a, state]
  have hnt' : nt ≤ 4 * (cut + 1) + 6 := by
    rw [hc3, hc4, List.length_replicate, List.length_replicate] at hnt
    exact hnt.trans (by omega)
  have h3' : (d.stacks 3).length ≤ degree scopes v + 1 := by simpa [hc3] using h3
  have h4' : (d.stacks 4).length ≤ cut + 1 := by simpa [hc4] using h4
  have hcleanCost : WorkspaceCleanupProgram.cost ([3, 4] : List (Fin 16)) e ≤
      2 * (degree scopes v + 1 + (cut + 1)) + 6 := by
    simp only [WorkspaceCleanupProgram.cost, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil]
    dsimp [e, emittedHigh]
    simp only [Function.update_of_ne (show (3 : Fin 16) ≠ 14 by decide),
      Function.update_of_ne (show (4 : Fin 16) ≠ 14 by decide)]
    omega
  rw [hcopylen]
  dsimp [queryBudget]
  omega

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
