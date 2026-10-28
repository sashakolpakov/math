import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CartesianMorphismIsomorphismComparison
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Relative Isomorphism Tensor Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.RelativeIsomorphismTensorCriterion

noncomputable section

/-! Isomorphism of the actual base-changed affine family morphism is
equivalent to bijectivity of its coefficient-tensor linear map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u
variable {R A C K : Type u} [CommRing R] [CommRing A] [CommRing C] [CommRing K]
variable [Algebra R A] [Algebra R C] [Algebra R K]

theorem affineRelativeBaseChange_isIso_iff_tensor (φ : A →ₐ[R] C) :
    IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (Spec.map (CommRingCat.ofHom φ.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ↔
        Function.Bijective (φ.toLinearMap.lTensor K) := by
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let u := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[R] K))
  let p := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : K →+* C ⊗[R] K))
  let v := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] K))
  let r := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : K →+* A ⊗[R] K))
  let ψ := Algebra.TensorProduct.map φ (AlgHom.id R K)
  let k := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hbase : f ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact φ.comp_algebraMap
  have hX : IsPullback u p (f ≫ q) g := by
    rw [hbase]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R C K)
  have hY : IsPullback v r q g :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R A K)
  have hk : k ≫ v = u ≫ f := by
    change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] K)) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[R] K)) ≫
          Spec.map (CommRingCat.ofHom φ.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact Algebra.TensorProduct.map_comp_includeLeftRingHom φ (AlgHom.id R K)
  have hr : k ≫ r = p := by
    change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : K →+* A ⊗[R] K)) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : K →+* C ⊗[R] K))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change ψ (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a
    simp only [ψ, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have he := CartesianMorphismIsomorphismComparison.relativeMorphismBaseChange_isIso_iff_cartesian_comparison f q g u p v r k hX hY hk hr
  have hi : IsIso k ↔ Function.Bijective (φ.toLinearMap.rTensor K) := by
    rw [isIso_SpecMap_iff]
    rfl
  exact he.trans (hi.trans (LinearMap.lTensor_bij_iff_rTensor_bij (M := K) (f := φ.toLinearMap)).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.RelativeIsomorphismTensorCriterion
