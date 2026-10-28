import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIncidence

namespace OAI.Algorithms

/-! Exact byte placement and reclamation for the executed incidence worker.
The source cutoff is computed by the staging command, independently of J. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage


private theorem destination_nodup : (pairs.map Prod.snd).Nodup := by
  simp [pairs]

private theorem separated : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.2 := by
  intro p hp q hq
  have hs : p.1.val < 340 ∨ 700 ≤ p.1.val := by
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
  have hd : 340 ≤ q.2.val ∧ q.2.val < 700 := by
    simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst q <;> decide
  intro he
  have hv := congrArg Fin.val he
  omega

private theorem destination_ne_cutoff : ∀ p ∈ pairs, p.2 ≠ 550 := by
  intro p hp
  simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

/-- All eighteen cache/master copies are exact when their destinations start
empty. This includes runtime theta, the merged assignment, and high context. -/
theorem staged_copy (a : Data) (hz : ∀ p ∈ pairs,a.stacks p.2 = [])
    (p : Fin 768 × Fin 768) (hp : p ∈ pairs) :
    (staged a).stacks p.2 = a.stacks p.1 := by
  change Function.update (copyManyState pairs a).stacks 550 _ p.2 = _
  rw [Function.update_of_ne (destination_ne_cutoff p hp)]
  exact copyMany_value pairs a destination_nodup hz separated p hp

theorem staged_frame (a : Data) (i : Fin 768) (hcut : i ≠ 550)
    (hi : ∀ p ∈ pairs,i ≠ p.2) : (staged a).stacks i = a.stacks i := by
  change Function.update (copyManyState pairs a).stacks 550 _ i = _
  rw [Function.update_of_ne hcut]
  exact copyMany_frame pairs a i hi

theorem staged_cutoff (a : Data) (R : ℕ)
    (hR : a.stacks 138 = List.replicate R true) (hz : a.stacks 550 = []) :
    (staged a).stacks 550 = List.replicate (R+1) true := by
  apply SourceControls.cutoff_value
  · rw [copyMany_frame pairs a 138]
    · exact hR
    · intro p hp
      simp only [pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
  · rw [copyMany_frame pairs a 550]
    · exact hz
    · intro p hp
      exact (destination_ne_cutoff p hp).symm

/-- The worker export copies the concrete table and clears every private
worker cell; global masters and branch/parser context are unchanged. -/
theorem exported_frame (a : Data) (i : Fin 768)
    (hi : i ∉ workerPorts) (hout : i ≠ 62) :
    (exported a).stacks i = a.stacks i := by
  rw [exported,clearMany_stacks,ite_eq_right hi]
  exact copyState_frame 561 62 i a hout

theorem exported_restores (a b : Data)
    (ha : ∀ i ∈ workerPorts,a.stacks i = []) (hout : b.stacks 62 = [])
    (hf : ∀ i,i ∉ workerPorts → i ≠ 62 → b.stacks i = a.stacks i) :
    (exported b).stacks = Function.update a.stacks 62 (b.stacks 561) := by
  funext i
  by_cases hi : i = 62
  · subst i; simpa using exported_output b hout
  rw [Function.update_of_ne hi]
  by_cases hw : i ∈ workerPorts
  · rw [exported,clearMany_stacks,ite_eq_left hw,ha i hw]
  · exact (exported_frame b i hw hi).trans (hf i hw hi)

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
