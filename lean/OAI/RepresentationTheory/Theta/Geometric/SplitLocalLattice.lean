import OAI.RepresentationTheory.Theta.Geometric.JointLocalLattice

/-! # Split Local Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The completed reference lattice is the product of its actual local
coordinate lattices. Integral split idempotents provide the missing
simultaneous-coordinate assertion. -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.jointLocalLattice_projection (u : Fin s × Bool → Fin 3 → ℚ_[q])
    (hu : u ∈ D.jointLocalLattice) (v : Fin s × Bool) : u v ∈ D.localReferenceLattice v := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => exact (D.localReferenceLattice v).zero_mem
  | add u w _ _ hu hw => exact (D.localReferenceLattice v).add_mem hu hw
  | smul c u _ hu => exact (D.localReferenceLattice v).smul_mem c hu

theorem Data.ActiveHeckeThetaData.jointLocalLattice_single (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (v : Fin s × Bool)
    (u : Fin 3 → ℚ_[q]) (hu : u ∈ D.localReferenceLattice v) :
    Pi.single v u ∈ D.jointLocalLattice := by
  let j : (Fin 3 → ℚ_[q]) →ₗ[ℤ_[q]] (Fin s × Bool → Fin 3 → ℚ_[q]) :=
    LinearMap.single ℤ_[q] (fun _ : Fin s × Bool => Fin 3 → ℚ_[q]) v
  change j u ∈ D.jointLocalLattice
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    have he : Data.ActiveHeckeThetaData.jointLocalScale (Pi.single v (1 : ℤ_[q])) (D.jointLocalEmbedding x) =
        j (fun i => D.localEmbedding v (x i)) := by
      funext w
      by_cases h : w = v
      · subst w
        simp [Data.ActiveHeckeThetaData.jointLocalScale, j, LinearMap.single_apply]
        rfl
      · simp [Data.ActiveHeckeThetaData.jointLocalScale, j, LinearMap.single_apply, h]
    rw [← he]
    exact D.jointLocalScale_mem hg hc hgood _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero =>
    rw [map_zero]
    exact D.jointLocalLattice.zero_mem
  | add u w _ _ hu hw =>
    rw [map_add]
    exact D.jointLocalLattice.add_mem hu hw
  | smul c u _ hu =>
    rw [map_smul]
    exact D.jointLocalLattice.smul_mem c hu

theorem Data.ActiveHeckeThetaData.jointLocalLattice_mem_iff (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (u : Fin s × Bool → Fin 3 → ℚ_[q]) :
    u ∈ D.jointLocalLattice ↔ ∀ v, u v ∈ D.localReferenceLattice v := by
  constructor
  · exact D.jointLocalLattice_projection u
  · intro hu
    have hsum : (∑ v, LinearMap.single ℤ_[q] (fun _ : Fin s × Bool => Fin 3 → ℚ_[q]) v (u v)) = u :=
      LinearMap.sum_single_apply (fun _ : Fin s × Bool => Fin 3 → ℚ_[q]) u
    rw [← hsum]
    exact D.jointLocalLattice.sum_mem (fun v _ => D.jointLocalLattice_single hg hc hgood v (u v) (hu v))

theorem Data.ActiveHeckeThetaData.jointLocalLattice_standard (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (u : Fin s × Bool → Fin 3 → ℚ_[q]) :
    u ∈ D.jointLocalLattice ↔ ∀ v, u v ∈ Data.ActiveHeckeThetaData.standardLocalLattice (q := q) := by
  rw [D.jointLocalLattice_mem_iff hg hc hgood]
  simp only [hc.2.1]

end

end OAI.RepresentationTheory.Theta.Geometric
