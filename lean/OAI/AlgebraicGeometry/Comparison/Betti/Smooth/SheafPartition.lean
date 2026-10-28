import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Locality
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf
import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication
import OAI.Analysis.DifferentialForms.Manifold.FinitePartition

/-! # Sheaf Partition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafPartition.Godement

noncomputable section

/-! Genuine smooth partitions act on the actual form sheaf by supported
endomorphisms whose sum is the identity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff BigOperators

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def smoothFormSheafMultiply (n : ℕ) (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) :
    Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n ⟶ Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction f hf.contMDiffOn)
      naturality {U V} i := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_smulByFunction (leOfHom i.unop)
          f hf.contMDiffOn a).symm }

theorem smoothFormSheafMultiply_vanishesOn (n : ℕ) (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) :
    Godement.Locality.VanishesOn (smoothFormSheafMultiply E M n f hf)
      ⟨(tsupport f)ᶜ, (isClosed_tsupport f).isOpen_compl⟩ := by
  intro U hU
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n at a
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction f hf.contMDiffOn a x = 0
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply, image_eq_zero_of_notMem_tsupport (hU x.property)]
  exact zero_smul ℂ (a x)

theorem smoothFormSheafMultiply_sum {ι : Type*} [Fintype ι] (n : ℕ) (f : ι → M → ℂ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (f i)) (hsum : ∀ x, ∑ i, f i x = 1) :
    ∑ i, smoothFormSheafMultiply E M n (f i) (hf i) = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U.unop n at a
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  let ev : (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n ⟶ Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n) →+
      (TangentSpace 𝓘(ℝ, E) x.val [⋀^Fin n]→L[ℝ] ℂ) :=
    { toFun := fun g => (show Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U.unop n from g.hom.app U a) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i, smoothFormSheafMultiply E M n (f i) (hf i)) = a x
  rw [map_sum]
  change ∑ i, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction (f i) (hf i).contMDiffOn a x = a x
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply]
  rw [← Finset.sum_smul, hsum, one_smul]

theorem exists_smoothFormSheaf_partition [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} [Fintype ι] (U : ι → Opens M) (hU : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    ∃ (V : ι → Opens M) (f : ι → (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n ⟶ Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n)),
      (∀ i, U i ⊔ V i = ⊤) ∧ (∀ i, Godement.Locality.VanishesOn (f i) (V i)) ∧ ∑ i, f i = 𝟙 _ := by
  obtain ⟨ρ, hρ, hsupp, hsum⟩ := Analysis.DifferentialForms.Manifold.FinitePartition.exists_finite_complex_partition
    (E := E) (fun i => (U i : Set M)) (fun i => (U i).isOpen) hU
  refine ⟨fun i => ⟨(tsupport (ρ i))ᶜ, (isClosed_tsupport (ρ i)).isOpen_compl⟩,
    fun i => smoothFormSheafMultiply E M n (ρ i) (hρ i), ?_, ?_,
    smoothFormSheafMultiply_sum E M n ρ hρ hsum⟩
  · intro i
    apply top_le_iff.mp
    intro x _
    by_cases hx : x ∈ tsupport (ρ i)
    · exact Or.inl (hsupp i hx)
    · exact Or.inr hx
  · exact fun i => smoothFormSheafMultiply_vanishesOn E M n (ρ i) (hρ i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafPartition.Godement
