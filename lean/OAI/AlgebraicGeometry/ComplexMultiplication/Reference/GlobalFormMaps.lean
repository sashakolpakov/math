import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.GlobalForms
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ClosedHolomorphicClasses

/-! # Global Form Maps -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalFormMaps

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Actual global original holomorphic forms map to genuine manifold forms -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
  (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))

/-- The genuine original holomorphic global-section complex maps to actual smooth forms. -/
def originalHolomorphicGlobalToManifoldNat :
    ((Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)).obj
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left))) ⟶
    ((Functor.mapHomologicalComplex (forget₂ (ModuleCat ℂ) AddCommGrpCat)
      (ComplexShape.up ℕ)).obj
        (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) (ComplexPoint.Basic.ComplexSchemePoint X))) :=
  ((Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)).map
    (ReferenceSmooth.FormSheaf.originalHolomorphicToSmoothSheafComplex X)) ≫ (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsNatIso X).hom

/-- The map's value is exactly the already proved full global tangent-form evaluation. -/
theorem originalHolomorphicGlobalToManifoldNat_f_apply (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤)) :
    (originalHolomorphicGlobalToManifoldNat X).f p θ =
      ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm X p θ := rfl

/-- The same actual map in the original integer-indexed global complexes. -/
def originalHolomorphicGlobalToManifoldInt :
    Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X) ⟶
      ReferenceSmooth.GlobalForms.originalManifoldDeRhamComplexInt X :=
  ((Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℤ)).map
    (ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X)) ≫ (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso X).hom

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero retains the exact natural-degree map, including all component transports. -/
theorem originalHolomorphicGlobalToManifoldInt_normalization :
    originalHolomorphicGlobalToManifoldInt X =
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ)
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) ComplexShape.embeddingUpNat).hom ≫
          HomologicalComplex.extendMap (originalHolomorphicGlobalToManifoldNat X)
            ComplexShape.embeddingUpNat := by
  have hn := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality (Γ)
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left))
      ComplexShape.embeddingUpNat (ReferenceSmooth.FormSheaf.originalHolomorphicToSmoothSheafComplex X)
  have hc := congrArg (fun g => g ≫ HomologicalComplex.extendMap
    (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsNatIso X).hom ComplexShape.embeddingUpNat) hn
  simpa only [originalHolomorphicGlobalToManifoldInt,
    ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt, ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso,
    Iso.trans_hom, Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map,
    Category.assoc, ← HomologicalComplex.extendMap_comp,
    originalHolomorphicGlobalToManifoldNat] using! hc

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalFormMaps
