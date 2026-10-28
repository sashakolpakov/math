import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixPositionProgram

namespace OAI.Algorithms

/-! Three physical byte comparisons for the selected joint coordinate. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 10 42

def eqRegs : Fin 5 → Fin 10 := Fin.castAdd 5
def eqStacks : Fin 13 → Fin 42 := Fin.castAdd 29
theorem eqRegs_injective : Function.Injective eqRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 10 => k.val) h)
theorem eqStacks_injective : Function.Injective eqStacks := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 42 => k.val) h)

abbrev equality : Cmd 10 42 := .call
  (ProgramLinking.liftProgram MatrixPositionProgram.equalityInner eqRegs eqStacks)

def compared (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
      11 (answer :: a.stacks 11)⟩

theorem equality_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 20,
      Eval equality n a (compared a (decide (a.stacks 1 = a.stacks 12))) := by
  let x : State 5 13 := ⟨fun j => a.regs (eqRegs j), fun j => a.stacks (eqStacks j)⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval x
  have hin : embedState eqRegs eqStacks a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqStacks_injective <;> intros <;> rfl
  have hout : embedState eqRegs eqStacks a
      (CollisionStreamProgram.sealed x (decide (x.stacks 1 = x.stacks 12))) =
      compared a (decide (a.stacks 1 = a.stacks 12)) := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqStacks_injective
    · intro j; fin_cases j <;> simp +decide [compared, CollisionStreamProgram.sealed, eqRegs]
    · intro j hj
      have hn : ¬ j.val < 5 := by
        intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [compared, hn]
    · intro j
      fin_cases j <;>
        simp +decide [compared, CollisionStreamProgram.sealed, x, eqStacks] ; rfl
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      have h12 : j ≠ 12 := fun h => hj ⟨12, h.symm⟩
      simp [compared, h1, h11, h12]
  have he := eval_call_lifted MatrixPositionProgram.equalityInner eqRegs eqStacks a
    eqRegs_injective eqStacks_injective (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · change n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 19 at hn
    omega
  · simpa only [hin, hout, equality] using he

def slot : Fin 4 → Fin 42 := ![38, 39, 40, 41]
abbrev copy (src dst : Fin 42) : Cmd 10 42 := .call (copyProgram src dst 0 0 1)
def copied (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

theorem copy_eval (a : Data) (src dst : Fin 42) (hsd : src ≠ dst)
    (hs0 : src ≠ 0) (h0d : (0 : Fin 42) ≠ dst) (h0 : a.stacks 0 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 0 (0 : Fin 10) 1 hsd hs0 h0d (by decide) a h0

abbrev pop : Cmd 10 42 := .base (.atom (.pop 11 3 4))
def popped (a : Data) : Data :=
  ⟨readRegs a.regs 3 4 (a.stacks 11).head?, Function.update a.stacks 11 (a.stacks 11).tail⟩
theorem pop_eval (a : Data) : Eval pop 1 a (popped a) := .base (.atom _ _)

abbrev setFalse : Cmd 10 42 := .base (.atom (.set 9 false))
abbrev accept (expected : Bool) : Cmd 10 42 :=
  if expected then .ite 3 (.base .skip) setFalse else .ite 3 setFalse (.base .skip)
def accepted (a : Data) (expected : Bool) : Data :=
  ⟨Function.update a.regs 9 (a.regs 9 && (a.regs 3 == expected)), a.stacks⟩

theorem accept_eval (a : Data) (expected : Bool) :
    ∃ n ≤ 2, Eval (accept expected) n a (accepted a expected) := by
  have ht : Eval setFalse 1 a ⟨Function.update a.regs 9 false, a.stacks⟩ := .base (.atom _ _)
  cases expected <;> cases ha : a.regs 3
  · refine ⟨1, by decide, ?_⟩
    simpa [accept, accepted, ha] using Eval.ite_false (yes := setFalse) ha
      (Eval.base (StructuredProgram.Eval.skip a))
  · refine ⟨2, by decide, ?_⟩
    simpa [accept, accepted, ha] using Eval.ite_true (no := .base .skip) ha ht
  · refine ⟨2, by decide, ?_⟩
    simpa [accept, accepted, ha] using Eval.ite_false (yes := .base .skip) ha ht
  · refine ⟨1, by decide, ?_⟩
    simpa [accept, accepted, ha] using Eval.ite_true (no := setFalse) ha
      (Eval.base (StructuredProgram.Eval.skip a))

abbrev check (left right : Fin 4) (expected : Bool) : Cmd 10 42 :=
  .seq (copy (slot left) 1) (.seq (copy (slot right) 12)
    (.seq equality (.seq pop (accept expected))))

theorem check_eval (a : Data) (left right : Fin 4) (expected : Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ 18 * (a.stacks (slot left)).length + 9 * (a.stacks (slot right)).length + 35,
      ∃ b : Data, Eval (check left right expected) n a b ∧ b.stacks = a.stacks ∧
        b.regs 9 = (a.regs 9 && (decide (a.stacks (slot left) = a.stacks (slot right)) == expected)) := by
  let a1 := copied a (slot left) 1
  let a2 := copied a1 (slot right) 12
  let answer := decide (a.stacks (slot left) = a.stacks (slot right))
  let a3 := compared a2 answer
  let a4 := popped a3
  let a5 := accepted a4 expected
  have t0 := copy_eval a (slot left) 1
    (by fin_cases left <;> decide) (by fin_cases left <;> decide) (by decide) h0
  have t1 := copy_eval a1 (slot right) 12
    (by fin_cases right <;> decide) (by fin_cases right <;> decide) (by decide)
    (by simp [a1, copied, copyStacks, h0])
  obtain ⟨ne, hne, te⟩ := equality_eval a2
  have hans : decide (a2.stacks 1 = a2.stacks 12) = answer := by
    fin_cases left <;> fin_cases right <;>
      simp +decide [a2, a1, copied, copyStacks, slot, h1, h12, answer] <;> rfl
  rw [hans] at te
  have tp := pop_eval a3
  obtain ⟨na, hna, ta⟩ := accept_eval a4 expected
  have he := t0.seq (t1.seq (te.seq (tp.seq ta)))
  refine ⟨_, ?_, a5, he, ?_, ?_⟩
  · fin_cases left <;> fin_cases right <;>
      simp +decide [a2, a1, copied, copyStacks, slot, h1, h12] at hne ⊢ <;> omega
  · funext j
    fin_cases j <;>
      simp +decide [a5, a4, a3, a2, a1, accepted, popped, compared, copied,
        copyStacks, h1, h11, h12]
  · simp +decide [a5, a4, a3, a2, a1, accepted, popped, compared, copied,
      readRegs, copyStacks, h11, answer]

abbrev command : Cmd 10 42 :=
  .seq (.base (.atom (.set 9 true)))
    (.seq (check 0 2 true) (.seq (check 1 2 false) (check 3 2 false)))

def valid (a : Data) : Bool :=
  decide (a.stacks 38 = a.stacks 40 ∧ a.stacks 39 ≠ a.stacks 40 ∧ a.stacks 41 ≠ a.stacks 40)

def cost (a : Data) : ℕ :=
  18 * ((a.stacks 38).length + (a.stacks 39).length + (a.stacks 41).length) +
    27 * (a.stacks 40).length + 106

theorem command_eval (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ cost a, ∃ b : Data, Eval command n a b ∧ b.stacks = a.stacks ∧ b.regs 9 = valid a := by
  let a0 : Data := ⟨Function.update a.regs 9 true, a.stacks⟩
  have ts : Eval (.base (.atom (.set 9 true))) 1 a a0 := .base (.atom _ _)
  obtain ⟨n1, hn1, a1, t1, hs1, hr1⟩ := check_eval a0 0 2 true h0 h1 h11 h12
  obtain ⟨n2, hn2, a2, t2, hs2, hr2⟩ := check_eval a1 1 2 false
    (by simpa [hs1, a0] using h0) (by simpa [hs1, a0] using h1)
    (by simpa [hs1, a0] using h11) (by simpa [hs1, a0] using h12)
  obtain ⟨n3, hn3, a3, t3, hs3, hr3⟩ := check_eval a2 3 2 false
    (by simpa [hs2, hs1, a0] using h0) (by simpa [hs2, hs1, a0] using h1)
    (by simpa [hs2, hs1, a0] using h11) (by simpa [hs2, hs1, a0] using h12)
  refine ⟨1 + (n1 + (n2 + n3)), ?_, a3, ts.seq (t1.seq (t2.seq t3)), ?_, ?_⟩
  · simp +decide [hs2, hs1, a0, slot, cost] at hn1 hn2 hn3 ⊢
    omega
  · exact hs3.trans (hs2.trans hs1)
  · rw [hr3, hr2, hr1, hs2, hs1]
    simp +decide [a0, slot, valid, Bool.and_assoc]
    rfl

def program := compiled command 38 38

theorem program_runsIn (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ b : Data, RunsIn program (cost a + 1)
      (a.withPC (some program.entry)) (b.withPC none) ∧ b.stacks = a.stacks ∧ b.regs 9 = valid a := by
  obtain ⟨n, hn, b, ht, hs, hr⟩ := command_eval a h0 h1 h11 h12
  exact ⟨b, ⟨n + 1, by omega, compiled_halt_trace ht 38 38⟩, hs, hr⟩

end SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

end OAI.Algorithms
