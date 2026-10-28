import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafPartition

/-! # Local Partition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.LocalPartition.Godement

noncomputable section

/-! Locally finite smooth partitions give local finite sums of supported
endomorphisms of the original smooth form sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff BigOperators _root_.Topology

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem smoothFormSheafMultiply_local_sum {ι : Type*} (n : ℕ) (f : ι → M → ℂ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (f i)) (s : Finset ι) (W : Opens M)
    (hsum : ∀ x ∈ W, ∑ i ∈ s, f i x = 1) :
    Godement.Locality.VanishesOn ((∑ i ∈ s, SheafPartition.Godement.smoothFormSheafMultiply E M n (f i) (hf i)) - 𝟙 _) W := by
  intro V hVW
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n at a
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  let ev : (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n ⟶ Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n) →+
      (TangentSpace 𝓘(ℝ, E) x.val [⋀^Fin n]→L[ℝ] ℂ) :=
    { toFun := fun g => (show Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n from g.hom.app (op V) a) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev ((∑ i ∈ s, SheafPartition.Godement.smoothFormSheafMultiply E M n (f i) (hf i)) - 𝟙 _) = 0
  rw [map_sub, map_sum]
  change (∑ i ∈ s, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction (f i) (hf i).contMDiffOn a x) - a x = 0
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply]
  rw [← Finset.sum_smul, hsum x.val (hVW x.property), one_smul, sub_self]

theorem exists_smoothFormSheaf_locally_finite_partition [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M] {ι : Type*}
    (U : ι → Opens M) (hU : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    ∃ (V : ι → Opens M) (f : ι → (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n ⟶ Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n)),
      (∀ i, U i ⊔ V i = ⊤) ∧ (∀ i, Godement.Locality.VanishesOn (f i) (V i)) ∧
      ∀ x : M, ∃ W : Opens M, x ∈ W ∧ ∃ s : Finset ι,
        (∀ i, i ∉ s → W ≤ V i) ∧ Godement.Locality.VanishesOn ((∑ i ∈ s, f i) - 𝟙 _) W := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) isClosed_univ (fun i => (U i : Set M)) (fun i => (U i).isOpen)
      (by intro x _; exact mem_iUnion.mpr (hU x))
  let g := Analysis.DifferentialForms.Manifold.FinitePartition.complexPartitionFunction ρ
  have hg := Analysis.DifferentialForms.Manifold.FinitePartition.complexPartitionFunction_smooth ρ
  let V : ι → Opens M := fun i => ⟨(tsupport (g i))ᶜ, (isClosed_tsupport (g i)).isOpen_compl⟩
  refine ⟨V, fun i => SheafPartition.Godement.smoothFormSheafMultiply E M n (g i) (hg i), ?_, ?_, ?_⟩
  · intro i
    apply top_le_iff.mp
    intro x _
    by_cases hx : x ∈ tsupport (g i)
    · exact Or.inl (hρ i ((Analysis.DifferentialForms.Manifold.FinitePartition.complexPartitionFunction_tsupport ρ i) ▸ hx))
    · exact Or.inr hx
  · exact fun i => SheafPartition.Godement.smoothFormSheafMultiply_vanishesOn E M n (g i) (hg i)
  · intro x
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp (ρ.eventually_fintsupport_subset x)
    refine ⟨⟨W, hWo⟩, hxW, ρ.fintsupport x, ?_, ?_⟩
    · intro i hi y hy hys
      have hs : y ∈ tsupport (ρ i) := (Analysis.DifferentialForms.Manifold.FinitePartition.complexPartitionFunction_tsupport ρ i) ▸ hys
      exact hi (hW hy ((ρ.mem_fintsupport_iff y i).mpr hs))
    · apply smoothFormSheafMultiply_local_sum
      intro y hy
      have hs : ∑ i ∈ ρ.fintsupport x, ρ i y = 1 :=
        ρ.sum_finsupport' y (mem_univ y) ((ρ.finsupport_subset_fintsupport y).trans (hW hy))
      change ∑ i ∈ ρ.fintsupport x, (ρ i y : ℂ) = 1
      exact_mod_cast hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.LocalPartition.Godement
