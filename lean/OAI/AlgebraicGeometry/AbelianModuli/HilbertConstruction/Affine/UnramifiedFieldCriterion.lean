import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FieldBaseChangeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Unramified Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.UnramifiedFieldCriterion

noncomputable section

/-! A finite-type morphism of affine schemes is formally unramified if all its field-valued base changes are formally unramified. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem specMap_formallyUnramified_of_fieldPullbacks {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [LocallyOfFiniteType (Spec.map φ)]
    (h : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec R),
      FormallyUnramified (Limits.pullback.snd (Spec.map φ) b)) : FormallyUnramified (Spec.map φ) := by
  have ht : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  algebraize [φ.hom]
  have : Algebra.FiniteType R S := ht
  apply (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr
  change Algebra.FormallyUnramified R S
  apply FieldBaseChangeCriterion.algebra_formallyUnramified_of_rightFieldBaseChanges R S
  intro K _ _
  let : Algebra K (S ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hf : FormallyUnramified (Limits.pullback.snd f b) := h K b
  have hi : FormallyUnramified ((pullbackSpecIso R S K).inv ≫ Limits.pullback.snd f b) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance hf
  have hs : FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap K (S ⊗[R] K)))) :=
    (pullbackSpecIso_inv_snd R S K) ▸ hi
  exact (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.UnramifiedFieldCriterion
