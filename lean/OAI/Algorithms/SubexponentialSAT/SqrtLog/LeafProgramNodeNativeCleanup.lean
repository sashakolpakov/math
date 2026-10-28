import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeCore

namespace OAI.Algorithms

/-! The paid node cleanup inspects its own workspace, never carried streams. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

def resultState (a : Data) (rr : Fin 40 → Bool) (entries jet : List Bool) : Data :=
  ⟨rr,Function.update (Function.update (Function.update a.stacks 163 []) 166 entries) 102 jet⟩

theorem resultState_machine (a : Data) (e : Product.Store) (rr : Fin 40 → Bool)
    (entries jet : List Bool)
    (hc : ∀ i : Fin 56,a.stacks (corePorts i)=Product.tapes e i) :
    machine rr e (Function.update (bucketStream a.stacks entries []) 102 jet)=
      resultState a rr entries jet := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i.val < 56
    · have h102 : i≠102 := by intro h; subst i; norm_num at hi
      have h163 : i≠163 := by intro h; subst i; norm_num at hi
      have h166 : i≠166 := by intro h; subst i; norm_num at hi
      let j : Fin 56 := ⟨i.val,hi⟩
      have hj : corePorts j=i := Fin.ext rfl
      simpa [machine,hi,resultState,bucketStream,h102,h163,h166,j,hj] using (hc j).symm
    · simp [hi,bucketStream,Function.update_comm (show (163:Fin 768)≠166 by decide)]

theorem resultState_frame {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (rr : Fin 40 → Bool) (entries jet : List Bool) (i : Fin 768)
    (hi : i∉Node.cleanupPorts) (ho : i≠102) :
    (resultState b rr entries jet).stacks i=a.stacks i := by
  have h163 : i≠163 := by intro h; subst i; exact hi ((Node.mem_cleanup _).mpr (by norm_num))
  have h166 : i≠166 := by intro h; subst i; exact hi ((Node.mem_cleanup _).mpr (by norm_num))
  simpa [resultState,ho,h163,h166] using pr.frame i hi

theorem cleaned_resultState {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (ha : Ready s a) (rr : Fin 40 → Bool) (entries jet : List Bool) :
    (Node.cleaned (resultState b rr entries jet)).stacks=
      Function.update (Function.update a.stacks 78 []) 102 jet := by
  simpa [resultState] using Node.cleaned_restores a (resultState b rr entries jet) ha.blank
    (resultState_frame pr rr entries jet)

theorem clearCost_le_workspace (is : List (Fin 768)) (a : Data) (W : ℕ)
    (ha : ∀ i∈is,(a.stacks i).length ≤ W) : Node.clearCost is a ≤ is.length*(2*W+3) := by
  induction is generalizing a with
  | nil => simp [Node.clearCost]
  | cons i is ih =>
    have hh := ih (LeafAssignmentSetupProgram.cleared a i) (by
      intro j hj
      by_cases hji : j=i
      · simp [LeafAssignmentSetupProgram.cleared,hji]
      · simpa [LeafAssignmentSetupProgram.cleared,hji] using ha j (by simp [hj]))
    have hi := ha i (by simp)
    simp only [Node.clearCost,List.length_cons]
    nlinarith

theorem resultState_cleanup_bound (a : Data) (rr : Fin 40 → Bool)
    (entries jet : List Bool) (W : ℕ)
    (ha : ∀ i∈Node.cleanupPorts,(a.stacks i).length ≤ W) (he : entries.length ≤ W) :
    Node.cleanupCost (resultState a rr entries jet) ≤ Node.cleanupPorts.length*(2*W+3) := by
  apply clearCost_le_workspace
  intro i hi
  have h102 : i≠102 := by intro h; subst i; norm_num [Node.mem_cleanup] at hi
  by_cases h166 : i=166
  · subst i; simpa [resultState] using he
  by_cases h163 : i=163
  · subst i; simp [resultState]
  simpa [resultState,h102,h163,h166] using ha i hi

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
