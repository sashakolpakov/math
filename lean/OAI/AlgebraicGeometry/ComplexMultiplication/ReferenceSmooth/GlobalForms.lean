import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Hypercohomology
import OAI.Algebra.Homology.MapExtend

/-! # Global Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.GlobalForms

noncomputable section

/-! # Actual smooth global forms recover the original additive global-section complex -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
  (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
local notation "F" => OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X
local notation "A" => forget₂ (ModuleCat ℂ) AddCommGrpCat
local notation "K" => OAI.Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex Model (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)

/-- The genuine manifold de Rham complex, with only its complex scalars forgotten. -/
def originalManifoldDeRhamComplexInt : CochainComplex AddCommGrpCat ℤ :=
  ((Functor.mapHomologicalComplex (A) (ComplexShape.up ℕ)).obj
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex Model (ComplexPoint.Basic.ComplexSchemePoint X))).extend ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
/-- In natural degrees, original additive global sections are the actual smooth forms. -/
def originalSmoothGlobalSectionsNatIso :
    ((Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)).obj
      ((Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ)).obj (K))) ≅
    ((Functor.mapHomologicalComplex (A) (ComplexShape.up ℕ)).obj
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex Model (ComplexPoint.Basic.ComplexSchemePoint X))) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (A).mapIso (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormGlobalSectionsIso Model (ComplexPoint.Basic.ComplexSchemePoint X) n))
    (by
      intro i j hij
      obtain rfl := hij
      simp only [Functor.mapHomologicalComplex_obj_d]
      rw [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d, Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d]
      apply AddCommGrpCat.hom_ext
      ext form
      exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_d form)

/-- Extending by zero retains the same genuine form identification in all integer degrees. -/
def originalSmoothGlobalSectionsIntIso :
    Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (Integration.originalSmoothDeRhamComplexInt X) ≅ originalManifoldDeRhamComplexInt X :=
  Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ)
    ((Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ)).obj (K))
      ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
      (originalSmoothGlobalSectionsNatIso X)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.GlobalForms
