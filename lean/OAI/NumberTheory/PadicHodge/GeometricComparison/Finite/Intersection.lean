import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Intersection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.Intersection.GeneralizedHecke

noncomputable section

/-! An arbitrary family of subspaces in finite dimension has the same intersection as a finite subfamily. -/

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem finite_intersection (S : I → Submodule K V) :
    ∃ s : Finset I, (⨅ i ∈ s, S i) = ⨅ i, S i := by
  classical
  obtain ⟨s, hs⟩ := exists_minimalFor_of_wellFoundedLT
    (fun _ : Finset I => True) (fun s => ⨅ i ∈ s, S i) ⟨∅, trivial⟩
  refine ⟨s, le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro i
    have hle : (⨅ j ∈ insert i s, S j) ≤ ⨅ j ∈ s, S j := by
      rw [Finset.iInf_insert]
      exact inf_le_right
    have hmin := hs.2 (show True from trivial) hle
    exact hmin.trans (iInf_le_of_le i (iInf_le _ (Finset.mem_insert_self i s)))
  · exact le_iInf fun i => le_iInf fun _ => iInf_le S i

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.Intersection.GeneralizedHecke
