import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramLayoutMasters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafSupportInputProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReadout
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost

namespace OAI.Algorithms

/-! The closed node worker: generate the actual head/bucket tables, stage the
ring caches, enumerate bounded supports, execute all assignment factors, and
read the resulting dense jet. Its final clear reclaims the node workspace.
The instruction table has no supplied node evaluator or precomputed jet. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Node
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def heads : Code := .call LeafHeadSetupProgram.Native.wideProgram
def supports : Code := .call LeafSupportInputProgram.program
def moments : Code := MomentsAssembly.denseCommand Factor.assignment

/-- The actual masters are outside this bank. The node input78 is consumed;
the dense output102 is the sole retained new value. Port104 remains empty,
which is an allowed shape in the indexed node collector. -/
def cleanupPorts : List (Fin 768) :=
  (List.finRange 768).filter fun i =>
    decide ((i.val < 142 ∧ i.val ≠ 102) ∨
      (143 ≤ i.val ∧ i.val < 192) ∨
      (340 ≤ i.val ∧ i.val < 700) ∨ (710 ≤ i.val ∧ i.val < 713))

def clearList : List (Fin 768) → Code
  | [] => .base .skip
  | i::is => .seq (LeafAssignmentSetupProgram.clear i) (clearList is)
def clearState : List (Fin 768) → Data → Data
  | [], a => a
  | i::is, a => clearState is (LeafAssignmentSetupProgram.cleared a i)
def clearCost : List (Fin 768) → Data → ℕ
  | [], _ => 0
  | i::is, a => 2*(a.stacks i).length+3+
      clearCost is (LeafAssignmentSetupProgram.cleared a i)

theorem clearList_eval (is : List (Fin 768)) (a : Data) :
    Eval (clearList is) (clearCost is a) a (clearState is a) := by
  induction is generalizing a with
  | nil => exact Eval.base (StructuredProgram.Eval.skip a)
  | cons i is ih => exact (LeafAssignmentSetupProgram.clear_eval a i).seq (ih _)

theorem clearState_stacks (is : List (Fin 768)) (a : Data) (i : Fin 768) :
    (clearState is a).stacks i = if i ∈ is then [] else a.stacks i := by
  induction is generalizing a with
  | nil => simp [clearState]
  | cons j js ih =>
      rw [clearState,ih]
      by_cases hj : i=j <;> by_cases hs : i∈js <;>
        simp [LeafAssignmentSetupProgram.cleared,hj,hs]

def cleanup : Code := clearList cleanupPorts
def cleaned (a : Data) : Data := clearState cleanupPorts a
def cleanupCost (a : Data) : ℕ := clearCost cleanupPorts a

def command : Code := .seq LayoutMasters.load (.seq heads
  (.seq LeafNodeCacheProgram.command (.seq supports (.seq moments cleanup))))
def program := compiled command 78 102

theorem cleanup_eval (a : Data) :
    Eval cleanup (cleanupCost a) a (cleaned a) := clearList_eval cleanupPorts a

theorem mem_cleanup (i : Fin 768) : i ∈ cleanupPorts ↔
    (i.val < 142 ∧ i.val ≠ 102) ∨ (143 ≤ i.val ∧ i.val < 192) ∨
    (340 ≤ i.val ∧ i.val < 700) ∨ (710 ≤ i.val ∧ i.val < 713) := by
  simp [cleanupPorts]

theorem cleaned_output (a : Data) : (cleaned a).stacks 102 = a.stacks 102 := by
  rw [cleaned,clearState_stacks,ite_eq_right (by
    intro h
    have hh := (mem_cleanup 102).mp h
    norm_num [Fin.coe_ofNat_eq_mod] at hh)]

theorem cleaned_node (a : Data) : (cleaned a).stacks 78 = [] := by
  rw [cleaned,clearState_stacks,ite_eq_left ((mem_cleanup 78).mpr (by norm_num [Fin.coe_ofNat_eq_mod]))]

theorem cleaned_shape (a : Data) : (cleaned a).stacks 104 = [] := by
  rw [cleaned,clearState_stacks,ite_eq_left ((mem_cleanup 104).mpr (by norm_num [Fin.coe_ofNat_eq_mod]))]

theorem cleaned_frame (a : Data) (i : Fin 768) (hi : i ∉ cleanupPorts) :
    (cleaned a).stacks i = a.stacks i := by
  rw [cleaned,clearState_stacks,ite_eq_right hi]

/-- The final exact frame follows from the actual component frames and the
blank reusable workspace. This lemma only describes the paid cleanup above. -/
theorem cleaned_restores (initial final : Data)
    (hblank : ∀ i ∈ cleanupPorts, i ≠ 78 → initial.stacks i = [])
    (hframe : ∀ i, i ∉ cleanupPorts → i ≠ 102 →
      final.stacks i = initial.stacks i) :
    (cleaned final).stacks =
      Function.update (Function.update initial.stacks 78 []) 102 (final.stacks 102) := by
  funext i
  by_cases ho : i = 102
  · subst i; simpa using cleaned_output final
  by_cases hn : i = 78
  · subst i; simpa using cleaned_node final
  simp only [Function.update_of_ne ho,Function.update_of_ne hn]
  by_cases hc : i ∈ cleanupPorts
  · rw [cleaned,clearState_stacks,ite_eq_left hc,hblank i hc hn]
  · exact (cleaned_frame final i hc).trans (hframe i hc ho)

/-- Every stage is the fixed native command above. The substantive input
contracts are supplied by those stages' checked execution theorems. -/
theorem command_eval (a a' b c d e : Data) (kl kh kc ks km : ℕ)
    (hl : Eval LayoutMasters.load kl a a')
    (hh : Eval heads kh a' b)
    (hc : Eval LeafNodeCacheProgram.command kc b c)
    (hs : Eval supports ks c d)
    (hm : Eval moments km d e) :
    Eval command (kl+(kh+(kc+(ks+(km+cleanupCost e))))) a (cleaned e) :=
  hl.seq (hh.seq (hc.seq (hs.seq (hm.seq (cleanup_eval e)))))

theorem clearCost_le (is : List (Fin 768)) (a : Data) (B : ℕ)
    (h : ∀ i, (a.stacks i).length ≤ B) :
    clearCost is a ≤ is.length*(2*B+3) := by
  induction is generalizing a with
  | nil => simp [clearCost]
  | cons i is ih =>
      have hn : ∀ j, ((LeafAssignmentSetupProgram.cleared a i).stacks j).length ≤ B := by
        intro j
        by_cases hj : j=i
        · simp [LeafAssignmentSetupProgram.cleared,hj]
        · simpa [LeafAssignmentSetupProgram.cleared,hj] using h j
      have hh := ih _ hn
      have hi := h i
      simp only [clearCost,List.length_cons]
      nlinarith

theorem cleanupCost_le (a : Data) (B : ℕ)
    (h : ∀ i, (a.stacks i).length ≤ B) :
    cleanupCost a ≤ cleanupPorts.length*(2*B+3) :=
  clearCost_le cleanupPorts a B h

end SubexponentialSAT.SqrtLog.LeafProgram.Node

end
end OAI.Algorithms
