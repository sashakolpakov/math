import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopWeight
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyInput

namespace OAI.Algorithms

/-! Explicit pure data conditions for the closed assignment adapter. The
engine field is a physical byte invariant, never an execution hypothesis. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open IdempotentApplyProgram.Bounds
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d : ℕ}

def assignmentEnvironment (q : Factor.Spec r Q n d) (degree : List Bool) : Product.Store :=
  Product.environment 3 q.p.t q.p.modulus q.p.cache q.ctx.table degree q.width q.u q.J

def assignmentMachine (q : Factor.Spec r Q n d) (degree : List Bool)
    (high : Fin 768 → List Bool) (left seed : Raw n (baseWidth 3 q.p.t) d)
    (regs : Fin 40 → Bool) : Factor.Data :=
  machine regs (Product.working (assignmentEnvironment q degree) left [] seed) high

def preparedAssignment (q : Factor.Spec r Q n d) (degree : List Bool)
    (high : Fin 768 → List Bool) (left seed : Raw n (baseWidth 3 q.p.t) d) : Fin 768 → List Bool :=
  (LeafAssignmentSetupProgram.prepared
    (assignmentMachine q degree high left seed (fun _=>false)) (fun _=>false) (fun _=>false)).stacks

theorem preparedAssignment_update (q : Factor.Spec r Q n d) (degree : List Bool)
    (high : Fin 768 → List Bool) (left seed : Raw n (baseWidth 3 q.p.t) d) :
    preparedAssignment q degree high left seed=
      Function.update (Function.update (preparedAssignment q degree high [] [])
        146 (Product.bytes left)) 147 (Product.bytes seed) := by
  funext i
  by_cases h146 : i=146
  · subst i; simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,assignmentMachine,machine,Product.working,Product.tapes]
  by_cases h147 : i=147
  · subst i; simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,assignmentMachine,machine,Product.working,Product.tapes]
  by_cases h145 : i=145
  · subst i; simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,assignmentMachine,machine]
  by_cases h148 : i=148
  · subst i; simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,LeafAssignmentSetupProgram.weight,assignmentMachine,machine]
  by_cases h40 : i=40
  · subst i; simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,assignmentMachine,machine]
  by_cases h42 : i=42
  · subst i; simp [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,assignmentMachine,machine]
  simp only [preparedAssignment,LeafAssignmentSetupProgram.prepared_stacks,
    Function.update_of_ne h146,Function.update_of_ne h147,Function.update_of_ne h145,
    Function.update_of_ne h148,Function.update_of_ne h40,Function.update_of_ne h42]
  simp only [assignmentMachine,machine]
  split_ifs with hi
  · have hn40 : (⟨i.val,hi⟩ : Fin 56)≠40 := by intro h; apply h40; exact Fin.ext (by simpa using congrArg (fun j : Fin 56 => j.val) h)
    have hn42 : (⟨i.val,hi⟩ : Fin 56)≠42 := by intro h; apply h42; exact Fin.ext (by simpa using congrArg (fun j : Fin 56 => j.val) h)
    simp [Product.working,Product.tapes,hn40,hn42]
  · rfl

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end

end OAI.Algorithms
