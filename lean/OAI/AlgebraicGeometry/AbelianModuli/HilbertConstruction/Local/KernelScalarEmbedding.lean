import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OneDimensionalKernelAugmentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.FunctionalLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductMapProjections
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Finiteness.Prod

/-! # Kernel Scalar Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.KernelScalarEmbedding

noncomputable section

/-! If the residue-field kernel of a map from a finite projective module to a finite free module has dimension at most one, its actual kernel embeds linearly in the local coefficient ring. -/

open scoped TensorProduct

universe u

theorem localKernel_exists_scalar_embedding
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N)
    (h : Module.finrank (IsLocalRing.ResidueField R) (f.baseChange (IsLocalRing.ResidueField R)).ker ≤ 1) :
    ∃ φ : f.ker →ₗ[R] R, Function.Injective φ := by
  let K := IsLocalRing.ResidueField R
  obtain ⟨a, ha⟩ := OneDimensionalKernelAugmentation.oneDimensionalKernel_exists_injective_augmentation (f.baseChange K) h
  have hs : Function.Surjective (algebraMap R K) := IsLocalRing.residue_surjective
  obtain ⟨l, hl⟩ := Scalar.FunctionalLift.scalarFunctional_exists_lift hs a
  have ht := Scalar.FunctionalLift.scalarFunctional_lift_tensor_identity a l hl
  let F := f.prod l
  have hi : Function.Injective (F.lTensor K) := by
    intro x y hxy
    apply ha
    apply Prod.ext
    · have H := congrArg ((LinearMap.fst R N R).lTensor K) hxy
      have H' : (f.lTensor K) x = (f.lTensor K) y := by
        simpa only [F, ← LinearMap.comp_apply, Tensor.ProductMapProjections.tensor_productMap_fst] using H
      exact H'
    · have H := congrArg ((LinearMap.snd R N R).lTensor K) hxy
      have H' : (l.lTensor K) x = (l.lTensor K) y := by
        simpa only [F, ← LinearMap.comp_apply, Tensor.ProductMapProjections.tensor_productMap_snd] using H
      have H'' := congrArg (TensorProduct.rid R K) H'
      change ((TensorProduct.rid R K).toLinearMap.comp (l.lTensor K)) x =
        ((TensorProduct.rid R K).toLinearMap.comp (l.lTensor K)) y at H''
      rw [ht] at H''
      exact H''
  obtain ⟨g, hg⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective F).mpr hi
  have hF : Function.Injective F := Function.LeftInverse.injective (fun x => LinearMap.congr_fun hg x)
  refine ⟨l.comp f.ker.subtype, fun x y hxy => ?_⟩
  apply Subtype.ext
  apply hF
  apply Prod.ext
  · exact x.property.trans y.property.symm
  · exact hxy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.KernelScalarEmbedding
