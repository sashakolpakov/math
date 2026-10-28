import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Global smooth gluing from actual smooth local extensions. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace OAI.Analysis.Calculus.SmoothExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_extension_of_local_on {K : Set E} (hK : IsClosed K)
    (u : E → F)
    (hl : ∀x ∈ K, ∃U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃g : E → F, ContDiffOn ℝ ∞ g U ∧ ∀y ∈ K ∩ U, g y = u y) :
    ∃g : E → F, ContDiff ℝ ∞ g ∧ ∀x ∈ K, g x = u x := by
  classical
  choose U hU hxU g hg heq using (fun x : K ↦ hl x x.property)
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ,E)) hK U hU (fun x hx ↦ mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩)
  refine ⟨fun x ↦ ∑ᶠi : K, ρ i x • g i x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    exact ρ.contDiffAt_finsum (fun i hi ↦
      (hg i).contDiffAt ((hU i).mem_nhds (hρ i hi)))
  · intro x hx
    calc
      (∑ᶠi : K, ρ i x • g i x) = ∑ᶠi : K, ρ i x • u x := by
        apply finsum_congr
        intro i
        by_cases hi : ρ i x = 0
        · simp [hi]
        · rw [heq i x ⟨hx,hρ i (subset_tsupport _ hi)⟩]
      _ = (∑i ∈ ρ.finsupport x, ρ i x) • u x := by
        rw [← ρ.sum_finsupport_smul_eq_finsum x (fun _ _ ↦ u x), Finset.sum_smul]
      _ = u x := by rw [ρ.sum_finsupport x hx,one_smul]

end OAI.Analysis.Calculus.SmoothExtension
