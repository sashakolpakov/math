import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWorkspace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidual

namespace OAI.Algorithms

/-! The outer branch loop changes only its counter and summation cells. The
invariant retains the actual prepared query tapes, and permits arbitrary mass
words so that the native adder's frame rule applies without a size assumption. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Branch
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Ports := LeafBranchProgram.Wide.fixedPorts

def mutable : List (Fin 768) := [323,324,330,331,332,333]
def Invariant (base a : Data) : Prop :=
  a.stacks 333=[] ∧ ∀ i,i∉mutable → a.stacks i=base.stacks i

theorem counterStable (base : Data) :
    CounterForPrograms.FrameStable Ports.counter (fun _ => Invariant base) := by
  intro j a b hab ha
  constructor
  · exact (hab 333 (by decide) (by decide)).symm.trans ha.1
  · intro i hi
    have h330 : i≠330 := fun h => hi (by simp [mutable,h])
    have h331 : i≠331 := fun h => hi (by simp [mutable,h])
    exact (hab i h330 h331).symm.trans (ha.2 i hi)

theorem massStable (base : Data) : LeafBranchProgram.MassStable Ports (Invariant base) := by
  intro a regs acc next ha
  constructor
  · exact (LeafBranchProgram.mass_frame Ports a regs acc next 333 (by decide)).trans ha.1
  · intro i hi
    have hf : ∀ j,Ports.mass.stack j≠i := by
      intro j h
      apply hi
      fin_cases j <;> simp [Ports,LeafBranchProgram.Wide.fixedPorts] at h <;> simp [mutable,←h]
    exact (LeafBranchProgram.mass_frame Ports a regs acc next i hf).trans (ha.2 i hi)

theorem initialized (base : Data) (regs : Fin 2 → Bool) :
    Invariant base (LeafBranchProgram.Wide.initialized base regs (base.stacks 333)) := by
  constructor
  · exact LeafBranchProgram.Wide.initialized_mask _ _ _
  · intro i hi
    exact LeafBranchProgram.Wide.initialized_frame _ _ _ i
      (fun h=>hi (by simp [mutable,h])) (fun h=>hi (by simp [mutable,h]))

theorem frame {base a : Data} (ha : Invariant base a) (i : Fin 768) (hi : i∉mutable) :
    a.stacks i=base.stacks i := ha.2 i hi

theorem restored {base a b : Data} (ha : Invariant base a)
    (hb : b.stacks=Function.update a.stacks 323 (b.stacks 323)) : Invariant base b := by
  constructor
  · have he := congrFun hb 333
    simp only [Function.update_of_ne (by decide : (333 : Fin 768)≠323)] at he
    exact he.trans ha.1
  · intro i hi
    have hn : i≠323 := fun h=>hi (by simp [mutable,h])
    have he := congrFun hb i
    simp only [Function.update_of_ne hn] at he
    exact he.trans (ha.2 i hi)

theorem finalProtected {base original a : Data} (ha : Invariant base a)
    (hbase : ∀ i,Query.Protected i → i≠323 → base.stacks i=original.stacks i) :
    Query.ProtectedWork original (Marked.Wide.workspace (LeafBranchProgram.Wide.finished a)) := by
  intro j hp
  let i := Marked.Wide.workPort j
  have hi : i∉mutable := by
    have h323 : i≠323 := Query.workspace_port_ne j 323 (by decide) (by decide)
    have h324 : i≠324 := Query.workspace_port_ne j 324 (by decide) (by decide)
    simp only [Query.Protected] at hp
    simp only [mutable,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨h323,h324,?_,?_,?_,?_⟩
    all_goals rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp
    all_goals omega
  have h321 : i≠321 := Query.workspace_port_ne j 321 (by decide) (by decide)
  have h323 : i≠323 := fun h=>hi (by simp [mutable,h])
  have h324 : i≠324 := fun h=>hi (by simp [mutable,h])
  have h330 : i≠330 := fun h=>hi (by simp [mutable,h])
  have h332 : i≠332 := fun h=>hi (by simp [mutable,h])
  exact (LeafBranchProgram.Wide.finished_frame a i h321 h323 h324 h330 h332).trans
    ((ha.2 i hi).trans (hbase i hp h323))

end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Branch

end OAI.Algorithms
