import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramCost
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! A single finite loop visits all runtime mask lengths. Its body is the
actual expansion and pruning program, not a semantic recursion instruction. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram.Loop

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open Steps

/-- The counter and registers are deliberately absent from the data invariant. -/
def Invariant (budget : List Bool) (n : ℕ) (a : Data) : Prop :=
  ∃ rows, Correct n budget.length rows ∧
    a.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords rows ∧
    a.stacks 1 = SubexponentialSAT.ProgramEncoding.encodeRecords alphabet ∧
    a.stacks 2 = [] ∧ a.stacks 3 = [] ∧ a.stacks 4 = [] ∧
    a.stacks 5 = [false] ∧ a.stacks 6 = [] ∧ a.stacks 7 = [] ∧ a.stacks 9 = budget

def ports : SubexponentialSAT.UnaryForPrograms.Ports 10 10 := ⟨8,8,9⟩
abbrev command : Cmd 10 10 := SubexponentialSAT.UnaryForPrograms.forCmd ports Steps.step
def stageCost (J n : ℕ) : ℕ := 1000 * (n + J + 1) * (count n J + 1)
def cost (n J : ℕ) : ℕ := n * stageCost J n + 2*n + 2

private theorem frameStable (budget : List Bool) :
    SubexponentialSAT.UnaryForPrograms.FrameStable ports (Invariant budget) := by
  intro n a b h hi
  rcases hi with ⟨rows,hc,h0,h1,h2,h3,h4,h5,h6,h7,h9⟩
  exact ⟨rows,hc,(h 0 (by decide)).symm.trans h0,(h 1 (by decide)).symm.trans h1,
    (h 2 (by decide)).symm.trans h2,(h 3 (by decide)).symm.trans h3,
    (h 4 (by decide)).symm.trans h4,(h 5 (by decide)).symm.trans h5,
    (h 6 (by decide)).symm.trans h6,(h 7 (by decide)).symm.trans h7,
    (h 9 (by decide)).symm.trans h9⟩

private theorem bodySpec (budget : List Bool) :
    SubexponentialSAT.UnaryForPrograms.BodySpec ports Steps.step (Invariant budget) (stageCost budget.length) := by
  intro n a hi
  rcases hi with ⟨rows,hc,h0,h1,h2,h3,h4,h5,h6,h7,h9⟩
  have hr : Ready budget rows (a.stacks 8) (a.regs 9) a :=
    ⟨⟨⟨h1,h3,h4,h6,h7,rfl,rfl⟩,h0,h2,h5⟩,h9⟩
  obtain ⟨m,b,hm,hb,he⟩ := Steps.step_eval budget rows (a.stacks 8) (a.regs 9) a hr
  have hcost := Steps.stepCost_le n budget rows (fun w hw => ((hc.2 w).mp hw).1.le)
  rw [correct_length n budget.length rows hc] at hcost
  rcases hb with ⟨⟨⟨hb1,hb3,hb4,hb6,hb7,hb8,hbg⟩,hb0,hb2,hb5⟩,hb9⟩
  exact ⟨m,b,hm.trans hcost,he,hb8,Steps.output budget rows,
    Steps.output_correct n budget rows hc,hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,hb9⟩

theorem stageCost_mono (J : ℕ) : Monotone (stageCost J) := by
  intro a b h
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 1000 (by omega))
    (Nat.add_le_add_right (count_mono_variables J h) 1)

theorem command_eval (budget : List Bool) (a : Data) (hi : Invariant budget 0 a) :
    ∃ m b, m ≤ cost (a.stacks 8).length budget.length ∧
      Invariant budget (a.stacks 8).length b ∧ b.stacks 8 = [] ∧ Eval command m a b := by
  obtain ⟨m,b,he,hb,hend,hm⟩ := SubexponentialSAT.UnaryForPrograms.for_correct ports Steps.step
    (Invariant budget) (stageCost budget.length) (frameStable budget) (bodySpec budget) a hi
  have hsum := SubexponentialSAT.CounterForPrograms.budgetSum_le_mono
    (stageCost budget.length) (stageCost_mono budget.length) (a.stacks 8).length
  exact ⟨m,b,by unfold cost; exact hm.trans (Nat.add_le_add_right (Nat.add_le_add_right hsum _) _),
    hb,hend,he⟩

def program := compiled command 0 0

/-- The same instruction table works for every n and J. The output masks are
complete and duplicate-free; the bound uses exactly the binomial support count. -/
theorem program_trace (budget : List Bool) (a : Data) (hi : Invariant budget 0 a) :
    ∃ (m : ℕ) (b : Data) (rows : Records), m ≤ cost (a.stacks 8).length budget.length + 1 ∧
      Correct (a.stacks 8).length budget.length rows ∧
      b.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords rows ∧
      b.stacks 8 = [] ∧ b.stacks 9 = budget ∧
      Trace program m (a.withPC (some program.entry)) (b.withPC none) := by
  obtain ⟨m,b,hm,hb,hend,he⟩ := command_eval budget a hi
  rcases hb with ⟨rows,hc,h0,h1,h2,h3,h4,h5,h6,h7,h9⟩
  exact ⟨m+1,b,rows,Nat.add_le_add_right hm 1,hc,h0,hend,h9,compiled_halt_trace he 0 0⟩

theorem cost_le (n J : ℕ) (hJ : 0 < J) :
    cost n J + 1 ≤ 3000 * (n + 1) * (n + J + 1) * count n J := by
  have hm : 1 ≤ count n J := by
    have he : List.replicate n false ∈ masks n J := by simp [List.count_replicate, hJ]
    have hp : 0 < (masks n J).length := List.length_pos_iff.mpr (by intro h; simp [h] at he)
    rw [masks_length] at hp
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp)
  have hdouble : count n J + 1 ≤ 2 * count n J := by omega
  have hfirst := Nat.mul_le_mul_left (n * 1000 * (n + J + 1)) hdouble
  have hone : 1 ≤ (n + J + 1) * count n J := by
    have hh := Nat.mul_le_mul (show 1 ≤ n + J + 1 by omega) hm
    simpa using hh
  have htail := Nat.mul_le_mul_left (3 * (n + 1)) hone
  unfold cost stageCost
  nlinarith

end SubexponentialSAT.SqrtLog.SupportProgram.Loop

end OAI.Algorithms
