import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramSourceCall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceConfiguration

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem sourceReady_index_frame {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a b : SourceBank.Data) (h : SourceBank.Ready p a)
    (hf : ∀ j : Fin 320, j≠304 → j≠305 → b.stacks j=a.stacks j) :
    SourceBank.Ready p b := by
  have hlow : SourceBank.lowStore b=SourceBank.lowStore a := by
    funext i
    apply hf
    all_goals
      intro he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      change i.val=_ at hv
      omega
  have hcleanup : ∀ j∈SourceBank.cleanupPorts, j≠304 ∧ j≠305 := by
    intro j hj
    simp [SourceBank.cleanupPorts] at hj
    constructor <;> intro h <;> subst j <;> simp at hj
  constructor
  · constructor
    · intro j hj hk
      rw [hf j (hcleanup j hj).1 (hcleanup j hj).2]
      exact h.work.work j hj hk
    · rw [hf 319 (by decide) (by decide)]; exact h.work.temp
    · rw [hf 287 (by decide) (by decide)]; exact h.work.output
    · rw [hf 37 (by decide) (by decide)]; exact h.work.count
    · rw [hf 64 (by decide) (by decide)]; exact h.work.tableCount
    · rw [hf 65 (by decide) (by decide)]; exact h.work.tableAccum
    · intro j hj
      rw [hf j (by intro he; subst j; norm_num at hj) (by intro he; subst j; norm_num at hj)]
      exact h.work.low j hj
  · intro u y
    exact SourceBank.inputFields_frame a b p.saved p.start u y (h.input u y) hlow
  · rw [hlow]; exact h.ring
  · rw [hf 252 (by decide) (by decide)]; exact h.inverseDenominator
  · rw [hf 22 (by decide) (by decide)]; exact h.nodes
  · rw [hf 47 (by decide) (by decide)]; exact h.limit
  · rw [hf 308 (by decide) (by decide)]; exact h.inverses
  · rw [hf 309 (by decide) (by decide)]; exact h.negatives
  · rw [hf 310 (by decide) (by decide)]; exact h.differences
  · rw [hf 311 (by decide) (by decide)]; exact h.ringWidth
  · rw [hf 312 (by decide) (by decide)]; exact h.rowWidth
  · rw [hf 313 (by decide) (by decide)]; exact h.zero
  · rw [hf 314 (by decide) (by decide)]; exact h.one

theorem source_fiber_projection (base : Store) (ids : List ℕ) (acc : List Bool) (i : ℕ) :
    (Function.update (fiberState base ids acc) 305 (List.replicate i true)) ∘ sourcePorts=
      Function.update (base ∘ sourcePorts) 305 (List.replicate i true) := by
  funext j
  have hp : (sourcePorts j).val < 320 := j.isLt
  have h328 : sourcePorts j≠328 := by intro he; rw [he] at hp; norm_num at hp
  have h329 : sourcePorts j≠329 := by intro he; rw [he] at hp; norm_num at hp
  have h333 : sourcePorts j≠333 := by intro he; rw [he] at hp; norm_num at hp
  have h305 : sourcePorts j=305 ↔ j=305 := by simp [sourcePorts,Fin.ext_iff]
  simp [Function.comp_def,fiberState,Function.update_apply,h328,h329,h333,h305]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
