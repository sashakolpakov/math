import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf
import OAI.Analysis.DifferentialForms.Manifold.ComplexSheafHomology
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Homology.Functor

/-! # Scalar Forget -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.ScalarForget

noncomputable section

/-! # Exactness of forgetting scalars on the actual smooth form sheaves

The functor is literal forgetting of complex scalars on every open section.
Limits and local preimages are retained, hence so is categorical homology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- Limits are detected on the actual underlying sheaf presheaves. -/
instance originalSmoothFormSheafForget_preservesFiniteLimits :
    PreservesFiniteLimits (FormSheaf.originalSmoothFormSheafForget X) where
  preservesFiniteLimits I _ _ := by
    have : PreservesLimitsOfShape I
        (FormSheaf.originalSmoothFormSheafForget X ⋙
          TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) := by
      change PreservesLimitsOfShape I
        (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (ModuleCat ℂ) ⋙
          (Functor.whiskeringRight (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ
            (ModuleCat ℂ) AddCommGrpCat).obj (forget₂ (ModuleCat ℂ) AddCommGrpCat))
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (FormSheaf.originalSmoothFormSheafForget X)
      (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))

/-- Forgetting complex scalars retains the actual local preimages defining epimorphisms. -/
instance originalSmoothFormSheafForget_preservesEpimorphisms :
    (FormSheaf.originalSmoothFormSheafForget X).PreservesEpimorphisms where
  preserves {F G} f hf := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi ((FormSheaf.originalSmoothFormSheafForget X).map f)).mp
    have h := (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr hf
    constructor
    intro U s
    exact h.imageSieve_mem s

/-- The literal scalar-forgetting functor preserves actual categorical homology. -/
instance originalSmoothFormSheafForget_preservesHomology :
    (FormSheaf.originalSmoothFormSheafForget X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (FormSheaf.originalSmoothFormSheafForget X)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.ScalarForget
