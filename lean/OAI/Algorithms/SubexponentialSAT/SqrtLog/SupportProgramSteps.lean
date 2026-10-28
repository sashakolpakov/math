import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramFilter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramGrowth
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-! One fixed expansion-and-pruning stage. The two-symbol alphabet is constant;
the length and support budget occur only in stack data. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram.Steps

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 10 10
abbrev Records := List (List Bool)
def alphabet : Records := [[false], [true]]
def tupleStacks (i : Fin 9) : Fin 10 := i.castSucc
def filterRegs (i : Fin 8) : Fin 10 := Fin.castAdd 2 i
def filterStacks : Fin 7 → Fin 10 := ![0,2,3,4,5,9,6]

theorem tupleStacks_injective : Function.Injective tupleStacks := Fin.castSucc_injective 9
theorem filterRegs_injective : Function.Injective filterRegs := Fin.castAdd_injective 8 2
theorem filterStacks_injective : Function.Injective filterStacks := by decide

def Ready (budget : List Bool) (rows : Records) (depth : List Bool) (guard : Bool)
    (a : Data) : Prop :=
  SubexponentialSAT.Subexp.TupleProgram.Ready alphabet rows depth guard (restrictState id tupleStacks a) ∧
    a.stacks 9 = budget

private theorem restrict_embed {r s R S : ℕ} (ρ : Fin r → Fin R) (σ : Fin s → Fin S)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ) (a : State R S) (b : State r s) :
    restrictState ρ σ (embedState ρ σ a b) = b := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; exact embedState_register ρ σ a b hρ i
  · funext i; exact embedState_stack ρ σ a b hσ i

def expandProgram := compiled SubexponentialSAT.Subexp.TupleProgram.expandStep 0 0
abbrev expand : Cmd 10 10 := .call (SubexponentialSAT.ProgramLinking.liftProgram expandProgram id tupleStacks)

theorem expand_eval (budget : List Bool) (rows : Records) (depth : List Bool)
    (guard : Bool) (a : Data) (ha : Ready budget rows depth guard a) :
    ∃ n b, n ≤ SubexponentialSAT.Subexp.TupleProgram.stepCost rows alphabet + 1 ∧
      Ready budget (cartesianOutput rows alphabet) depth guard b ∧ Eval expand n a b := by
  obtain ⟨n, small, hn, hs, he⟩ := SubexponentialSAT.Subexp.TupleProgram.expandStep_eval
    alphabet rows depth guard (restrictState id tupleStacks a) ha.1
  obtain ⟨m, hm, ht⟩ := lifted_call expandProgram id tupleStacks Function.injective_id
    tupleStacks_injective a small (SubexponentialSAT.Subexp.TupleProgram.stepCost rows alphabet + 1)
    ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 0 0⟩
  refine ⟨m, embedState id tupleStacks a small, hm, ⟨?_, ?_⟩, ht⟩
  · rw [restrict_embed id tupleStacks Function.injective_id tupleStacks_injective]
    exact hs
  · rw [embedState_stack_frame]
    · exact ha.2
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      change i.val = 9 at hv
      have hlt := i.isLt
      omega

abbrev filter : Cmd 10 10 := .call (SubexponentialSAT.ProgramLinking.liftProgram Filter.program filterRegs filterStacks)

abbrev restore : Cmd 10 10 :=
  .seq (.call (SubexponentialSAT.StackRoutines.transferProgram 5 7 6 7))
    (.seq (.call (SubexponentialSAT.StackRoutines.transferProgram 7 0 6 7)) (pushConst 5 6 false))

def filtered (budget : List Bool) (rows : Records) : Records :=
  (rows.filter (Filter.keep budget.length)).reverse

abbrev step : Cmd 10 10 := .seq expand (.seq filter restore)
def output (budget : List Bool) (rows : Records) : Records :=
  filtered budget (cartesianOutput rows alphabet)

theorem filter_restore_eval (budget : List Bool) (rows : Records) (depth : List Bool)
    (guard : Bool) (a : Data) (ha : Ready budget rows depth guard a) :
    ∃ n b, n ≤ Filter.cost budget rows +
        6 * (SubexponentialSAT.ProgramEncoding.encodeRecords (filtered budget rows)).length + 9 ∧
      Ready budget (filtered budget rows) depth guard b ∧
      Eval (.seq filter restore) n a b := by
  rcases ha with ⟨⟨⟨h1,h3,h4,h6,h7,h8,hg⟩,h0,h2,h5⟩,h9⟩
  have hi : Filter.invariant budget (restrictState filterRegs filterStacks a) :=
    ⟨h3,h4,h9,h6⟩
  obtain ⟨small, hs, hs0, hs1, hs4, ht⟩ := Filter.program_runsIn budget rows []
    (restrictState filterRegs filterStacks a) hi h0 h2 h5
  obtain ⟨q,hq,he⟩ := lifted_call Filter.program filterRegs filterStacks
    filterRegs_injective filterStacks_injective a small (Filter.cost budget rows + 1) ht
  let b := embedState filterRegs filterStacks a small
  have hstk (i : Fin 7) : b.stacks (filterStacks i) = small.stacks i :=
    embedState_stack filterRegs filterStacks a small filterStacks_injective i
  have hb0 : b.stacks 0 = [] := (hstk 0).trans hs0
  have hb2 : b.stacks 2 = [] := (hstk 1).trans hs1
  have hb3 : b.stacks 3 = [] := (hstk 2).trans hs.1
  have hb4 : b.stacks 4 = [] := (hstk 3).trans hs.2.1
  have hb5 : b.stacks 5 = SubexponentialSAT.ProgramEncoding.encodeRecords (filtered budget rows) := by
    simpa [filtered, filterStacks] using (hstk 4).trans hs4
  have hb9 : b.stacks 9 = budget := (hstk 5).trans hs.2.2.1
  have hb6 : b.stacks 6 = [] := (hstk 6).trans hs.2.2.2
  have hb1 : b.stacks 1 = a.stacks 1 :=
    embedState_stack_frame _ _ _ _ _ (by decide)
  have hb7 : b.stacks 7 = a.stacks 7 :=
    embedState_stack_frame _ _ _ _ _ (by decide)
  have hb8 : b.stacks 8 = a.stacks 8 :=
    embedState_stack_frame _ _ _ _ _ (by decide)
  have hbg : b.regs 9 = a.regs 9 :=
    embedState_register_frame _ _ _ _ _ (by decide)
  let c : Data := ⟨readRegs b.regs 6 7 none, SubexponentialSAT.StackRoutines.transferStacks 5 7 b.stacks⟩
  let d : Data := ⟨readRegs c.regs 6 7 none, SubexponentialSAT.StackRoutines.transferStacks 7 0 c.stacks⟩
  let e := pushedState 5 6 false d
  have hfirst := transfer_eval 5 7 6 7 (by decide) (by decide) b
  have hsecond := transfer_eval 7 0 6 7 (by decide) (by decide) c
  have hthird := pushConst_eval 5 6 false d
  have hc7 : (c.stacks 7).length = (b.stacks 5).length := by
    change a.stacks 7 = [] at h7
    simp [c, SubexponentialSAT.StackRoutines.transferStacks, hb7, h7]
  refine ⟨q + ((3 * (b.stacks 5).length + 3) +
    ((3 * (c.stacks 7).length + 3) + 2)), e, ?_, ?_, he.seq (hfirst.seq (hsecond.seq hthird))⟩
  · rw [hc7, hb5]
    omega
  · change a.stacks 1 = _ at h1
    change a.stacks 7 = [] at h7
    change a.stacks 8 = depth at h8
    change a.regs 9 = guard at hg
    simp [Ready, SubexponentialSAT.Subexp.TupleProgram.Ready, outerInvariant, restrictState, tupleStacks,
      e, d, c, SubexponentialSAT.StackRoutines.transferStacks, readRegs,
      hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,hb8,hb9,hbg,h1,h7,h8,hg]

def stepCost (budget : List Bool) (rows : Records) : ℕ :=
  SubexponentialSAT.Subexp.TupleProgram.stepCost rows alphabet +
    Filter.cost budget (cartesianOutput rows alphabet) +
    6 * (SubexponentialSAT.ProgramEncoding.encodeRecords (output budget rows)).length + 10

theorem step_eval (budget : List Bool) (rows : Records) (depth : List Bool)
    (guard : Bool) (a : Data) (ha : Ready budget rows depth guard a) :
    ∃ n b, n ≤ stepCost budget rows ∧ Ready budget (output budget rows) depth guard b ∧
      Eval step n a b := by
  obtain ⟨n,b,hn,hb,he⟩ := expand_eval budget rows depth guard a ha
  obtain ⟨m,c,hm,hc,hf⟩ := filter_restore_eval budget (cartesianOutput rows alphabet) depth guard b hb
  exact ⟨n+m,c,by dsimp [stepCost, output] at *; omega,hc,he.seq hf⟩

end SubexponentialSAT.SqrtLog.SupportProgram.Steps

end OAI.Algorithms
