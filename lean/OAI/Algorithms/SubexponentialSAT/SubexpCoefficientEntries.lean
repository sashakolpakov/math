import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientStaging

namespace OAI.Algorithms

/-! Small portwise entry proofs for the coefficient adapter's actual calls. -/

namespace SubexponentialSAT.SubexpCoefficientStaging.Stage

open StructuredCalls SubexpSetupStorage

theorem prepared_word (s : Stage) (a : Data) (p : Fin 64 × Fin 64)
    (hp : p ∈ s.inputs) : (s.prepared a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ s.inputs, (beforeCopies 63 s.work a).stacks q.2 = [] := by
    intro q hq
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_left ((s.mem_work q.2).mpr (s.target_low q hq))]
  have hv := copyMany_value s.inputs (beforeCopies 63 s.work a)
    s.inputs_nodup hc s.inputs_separated p hp
  change (s.prepared a).stacks p.2 = _ at hv
  rw [hv]
  have hh := s.source_high p hp
  have hn : p.1 ∉ s.work := by rw [s.mem_work]; have := s.stack_le; omega
  have ht : p.1 ≠ 63 := by
    intro h
    have hv := congrArg (fun i : Fin 64 => i.val) h
    norm_num at hv
    omega
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_right hn]
  simp [ht]

theorem prepared_empty (s : Stage) (a : Data) (i : Fin 64)
    (hi : i.val < s.stackCount) (hd : ∀ p ∈ s.inputs, i ≠ p.2) :
    (s.prepared a).stacks i = [] := by
  unfold prepared prepareState
  rw [copyMany_frame _ _ _ hd]
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_left ((s.mem_work i).mpr hi)]

theorem project_eq (s : Stage) (a : Data) (out : State s.registers s.stackCount)
    (hr : ∀ i, (s.prepared a).regs (s.register i) = out.regs i)
    (hw : ∀ p ∈ s.inputs, ∀ j, s.stack j = p.2 → out.stacks j = a.stacks p.1)
    (hz : ∀ j, (∀ p ∈ s.inputs, s.stack j ≠ p.2) → out.stacks j = []) :
    project s.register s.stack (s.prepared a) = out := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    exact hr i
  · funext j
    by_cases hm : ∃ p ∈ s.inputs, s.stack j = p.2
    · obtain ⟨p, hp, hj⟩ := hm
      change (s.prepared a).stacks (s.stack j) = out.stacks j
      rw [hj, s.prepared_word a p hp, hw p hp j hj]
    · have hd : ∀ p ∈ s.inputs, s.stack j ≠ p.2 := by
        intro p hp hj
        exact hm ⟨p, hp, hj⟩
      exact (s.prepared_empty a (s.stack j) j.isLt hd).trans (hz j hd).symm

end SubexponentialSAT.SubexpCoefficientStaging.Stage

end OAI.Algorithms
