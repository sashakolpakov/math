import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsoFrameTensorFormula

/-! # Line Morphism Equiv -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.LineMorphismEquiv

noncomputable section

/-! Tensoring by an actual line bundle preserves and reflects all
module-sheaf morphisms. The equivalence's map is the original binary
tensor map, so its inverse cancels a generating twist on morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {X : Scheme.{u}}

local instance tensorLineMorphism_monoidal : MonoidalCategory X.Modules :=
  SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def tensorLineMorphismEquiv (M N : X.Modules) (H : HilbertConstruction.Line.Bundles.LineBundle X) :
    (M ⟶ N) ≃ (HilbertConstruction.Tensor.ProductSheaf.tensorModule M H.sheaf ⟶ HilbertConstruction.Tensor.ProductSheaf.tensorModule N H.sheaf) := by
  let F := SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence H.sheaf (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible H)
  let eM : F.functor.obj M ≅ HilbertConstruction.Tensor.ProductSheaf.tensorModule M H.sheaf := SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M H.sheaf
  let eN : F.functor.obj N ≅ HilbertConstruction.Tensor.ProductSheaf.tensorModule N H.sheaf := SheafCohomology.Projective.TensorSections.monoidalTensorObjIso N H.sheaf
  exact F.fullyFaithfulFunctor.homEquiv.trans (eM.homFromEquiv.trans eN.homToEquiv)

theorem tensorLineMorphismEquiv_apply (M N : X.Modules) (H : HilbertConstruction.Line.Bundles.LineBundle X) (f : M ⟶ N) :
    tensorLineMorphismEquiv M N H f = HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H.sheaf) := by
  change ((SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M H.sheaf).inv ≫
    (SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence H.sheaf (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible H)).functor.map f) ≫
      (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso N H.sheaf).hom = _
  rw [SheafCohomology.Projective.InvertibleRightTensorMap.invertibleRightTensorEquivalence_map, ← tensorHom_id]
  have h := congrArg (fun a => a ≫ (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso N H.sheaf).hom)
    (SheafCohomology.Projective.TensorFrameSections.monoidalTensorObjIso_inv_natural f (𝟙 H.sheaf))
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc] at h
  erw [Category.assoc]
  exact h.symm.trans (IsoFrameTensorFormula.isoFrame_tensorMap_eq f (𝟙 H.sheaf)).symm

theorem tensorLineMorphism_surjective (M N : X.Modules) (H : HilbertConstruction.Line.Bundles.LineBundle X)
    (g : HilbertConstruction.Tensor.ProductSheaf.tensorModule M H.sheaf ⟶ HilbertConstruction.Tensor.ProductSheaf.tensorModule N H.sheaf) :
    ∃ f : M ⟶ N, HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H.sheaf) = g := by
  obtain ⟨f, hf⟩ := (tensorLineMorphismEquiv M N H).surjective g
  exact ⟨f, (tensorLineMorphismEquiv_apply M N H f).symm.trans hf⟩

theorem tensorLineMorphism_injective (M N : X.Modules) (H : HilbertConstruction.Line.Bundles.LineBundle X) :
    Function.Injective (fun f : M ⟶ N => HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H.sheaf)) := by
  intro f g h
  apply (tensorLineMorphismEquiv M N H).injective
  exact (tensorLineMorphismEquiv_apply M N H f).trans
    (h.trans (tensorLineMorphismEquiv_apply M N H g).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.LineMorphismEquiv
