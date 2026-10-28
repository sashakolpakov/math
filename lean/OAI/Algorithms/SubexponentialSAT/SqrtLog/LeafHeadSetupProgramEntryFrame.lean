import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramEntryReady

namespace OAI.Algorithms

/-! All twelve entry-cache sources are invariant during the head loop.
Consequently the actual boot cache needs a single native entry contract. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem matrixEntry_prepared_eq (base b : Data) (hf : LoopFrame base b)
    (rp : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (regs : Fin 16 → Bool) (row col pos neg : List Bool) :
    LayoutMatrixProgram.entryState (matrixBase (preparedHead b rp n N rows low W z))
      regs row col pos neg=
    LayoutMatrixProgram.entryState (matrixBase base) regs row col pos neg := by
  have hs (i : Fin 768) (hi : Protected i) (hn : i∉loopMutable) :
      (preparedHead b rp n N rows low W z).stacks i=base.stacks i := by
    have hns : i≠650 ∧ i≠651 ∧ i≠652 ∧ i≠670 ∧ i≠671 := by
      simp only [loopMutable,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
      exact ⟨hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
    exact (preparedHead_frame b rp n N rows low W z i hi hns.1 hns.2.1 hns.2.2.1
      hns.2.2.2.1 hns.2.2.2.2).trans (hf i hi hn)
  have h135 := hs 135 (by decide) (by simp [loopMutable])
  have h136 := hs 136 (by decide) (by simp [loopMutable])
  have h640 := hs 640 (by decide) (by simp [loopMutable])
  have h641 := hs 641 (by decide) (by simp [loopMutable])
  have h140 := hs 140 (by decide) (by simp [loopMutable])
  have h642 := hs 642 (by decide) (by simp [loopMutable])
  have h138 := hs 138 (by decide) (by simp [loopMutable])
  have h139 := hs 139 (by decide) (by simp [loopMutable])
  have h130 := hs 130 (by decide) (by simp [loopMutable])
  have h131 := hs 131 (by decide) (by simp [loopMutable])
  have h307 := hs 307 (by decide) (by simp [loopMutable])
  have h132 := hs 132 (by decide) (by simp [loopMutable])
  apply congrArg (StructuredProgram.State.mk regs)
  funext i
  have hn (j : Fin 288) (hj : j.val < 25) : LayoutMatrixProgram.bankPort i≠j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [LayoutMatrixProgram.bankPort] at hv
    omega
  simp only [matrixBase,
    ite_eq_right (hn 0 (by decide)),ite_eq_right (hn 17 (by decide)),ite_eq_right (hn 18 (by decide)),
    ite_eq_right (hn 23 (by decide)),h135,h136,h640,h641,h140,h642,h138,h139,h130,h131,h307,h132]

theorem entryContract_prepared (entry : Cmd 16 256) (base b : Data) (hf : LoopFrame base b)
    (rp : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : LayoutMatrixProgram.EntryContract entry (matrixBase base) Valid Rel T B) :
    LayoutMatrixProgram.EntryContract entry (matrixBase (preparedHead b rp n N rows low W z))
      Valid Rel T B := by
  intro regs j v hv
  simpa only [matrixEntry_prepared_eq base b hf rp n N W z rows low] using hc regs j v hv

theorem nodeEntry_of_initial (entry : Cmd 16 256) (a : Data) (n N W r t : ℕ)
    (records rows : List (List Bool)) (low height R width : List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : ∀ ra rd rc words,CacheCorrect height R width words →
      LayoutMatrixProgram.EntryContract entry
        (matrixBase (nodeStart a ra rd rc r t records height R width words)) Valid Rel T B) :
    NodeEntry entry a n N W r t records rows low height R width Valid Rel T B := by
  intro ra rd rc words hw b z rp hf
  exact entryContract_prepared entry _ b hf rp n N W z rows low Valid Rel T B (hc ra rd rc words hw)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
