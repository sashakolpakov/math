import OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSingularGlobalRestriction
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalIntegrationClasses
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularSmoothRestriction

/-! # Ordinary Smooth Global Units -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.OrdinarySmoothGlobalUnits

noncomputable section

/-! # Actual ordinary cochains and original smooth hyperclasses

Only complex module scalars are forgotten. Integer degrees use the canonical
extension-by-zero transport, and every unit is actual sheafification.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
  (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
local notation "mapA" => Functor.mapHomologicalComplex
  (forget₂ (ModuleCat ℂ) AddCommGrpCat) (ComplexShape.up ℕ)
local notation "mapF" => Functor.mapHomologicalComplex
  (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X) (ComplexShape.up ℕ)
local notation "ΓNat" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)
local notation "ΓInt" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℤ)
local notation "O" => Functor.obj (mapF) (OAI.AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex Y)
local notation "S" => Functor.obj (mapF)
  (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex Model M (ModuleCat.of ℂ ℂ))

/-- Genuine ambient ordinary cochains, retaining the original point space. -/
def originalOrdinaryAmbientCochainsNat : CochainComplex AddCommGrpCat ℕ :=
  (mapA).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) Y)

/-- Ambient ordinary cochains extended by zero to integer degrees. -/
def originalOrdinaryAmbientCochainsInt : CochainComplex AddCommGrpCat ℤ :=
  (originalOrdinaryAmbientCochainsNat X).extend ComplexShape.embeddingUpNat

/-- Actual ordinary ambient cochains enter genuine global sheaf sections. -/
def originalOrdinaryGlobalUnitNat :
    originalOrdinaryAmbientCochainsNat X ⟶ (ΓNat).obj (O) :=
  (mapA).map (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) Y)

/-- The ordinary unit in integer degrees uses the canonical global-section transport. -/
def originalOrdinaryGlobalUnitInt :
    originalOrdinaryAmbientCochainsInt X ⟶
      Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y (SingularSmoothRestriction.originalOrdinarySingularComplexInt X) :=
  HomologicalComplex.extendMap (originalOrdinaryGlobalUnitNat X) ComplexShape.embeddingUpNat ≫
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (O) ComplexShape.embeddingUpNat).inv

/-- Genuine restriction to actual smooth simplices on the unchanged original atlas. -/
def originalOrdinaryToSmoothAmbientNat :
    originalOrdinaryAmbientCochainsNat X ⟶
      (mapA).obj (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains Model (ModuleCat.of ℂ ℂ) M) :=
  (mapA).map (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction Model
    (ModuleCat.of ℂ ℂ) M)

/-- The same actual smooth-simplex restriction extended by zero. -/
def originalOrdinaryToSmoothAmbientInt :
    originalOrdinaryAmbientCochainsInt X ⟶ GlobalIntegrationClasses.originalManifoldSmoothCochainsInt X :=
  HomologicalComplex.extendMap (originalOrdinaryToSmoothAmbientNat X)
    ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
/-- Both original global units commute with actual smooth-simplex restriction. -/
theorem originalOrdinarySmoothGlobalUnitNat_square :
    originalOrdinaryGlobalUnitNat X ≫
        (ΓNat).map ((mapF).map (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction
          Model M (ModuleCat.of ℂ ℂ))) =
      originalOrdinaryToSmoothAmbientNat X ≫ GlobalIntegrationClasses.originalSmoothGlobalUnitNat X := by
  simpa only [Functor.map_comp] using! congrArg (fun f => (mapA).map f)
    (ConcreteSingularGlobalRestriction.actualSingularGlobalRestriction_square Model M)

set_option backward.isDefEq.respectTransparency false in
/-- Canonical integer transport retains the original ordinary/smooth unit square. -/
theorem originalOrdinarySmoothGlobalUnitInt_square :
    originalOrdinaryGlobalUnitInt X ≫
        (ΓInt).map (SingularSmoothRestriction.originalOrdinaryToSmoothSheafRestrictionInt X) =
      originalOrdinaryToSmoothAmbientInt X ≫ GlobalIntegrationClasses.originalSmoothGlobalUnitInt X := by
  apply (cancel_mono
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (S) ComplexShape.embeddingUpNat).hom).1
  simp only [originalOrdinaryGlobalUnitInt, GlobalIntegrationClasses.originalSmoothGlobalUnitInt,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality (Γ) (O)
    ComplexShape.embeddingUpNat
      ((mapF).map (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction
        Model M (ModuleCat.of ℂ ℂ)))
  change HomologicalComplex.extendMap (originalOrdinaryGlobalUnitNat X)
      ComplexShape.embeddingUpNat ≫
        ((Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (O) ComplexShape.embeddingUpNat).inv ≫
          ((ΓInt).map (HomologicalComplex.extendMap
            ((mapF).map (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction
              Model M (ModuleCat.of ℂ ℂ))) ComplexShape.embeddingUpNat) ≫
                (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (S)
                  ComplexShape.embeddingUpNat).hom)) = _
  rw [hn, Iso.inv_hom_id_assoc, ← HomologicalComplex.extendMap_comp,
    originalOrdinarySmoothGlobalUnitNat_square, HomologicalComplex.extendMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Actual ordinary global classes retain their smooth-singular hyperclasses in every degree. -/
theorem originalOrdinarySmoothGlobalUnit_hyperClass (n : ℤ)
    (z : (originalOrdinaryAmbientCochainsInt X).homology n) :
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (SingularSmoothRestriction.originalOrdinaryToSmoothSheafRestrictionInt X) n
        (GlobalNaturality.globalSectionsToHypercohomology X (SingularSmoothRestriction.originalOrdinarySingularComplexInt X) n
          (HomologicalComplex.homologyMap (originalOrdinaryGlobalUnitInt X) n z)) =
      GlobalNaturality.globalSectionsToHypercohomology X (ReferenceSmooth.Integration.originalSmoothSingularComplexInt X) n
        (HomologicalComplex.homologyMap (GlobalIntegrationClasses.originalSmoothGlobalUnitInt X) n
          (HomologicalComplex.homologyMap (originalOrdinaryToSmoothAmbientInt X) n z)) := by
  rw [← GlobalNaturality.globalSectionsToHypercohomology_naturality]
  have he := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (originalOrdinarySmoothGlobalUnitInt_square X)
  simp only [HomologicalComplex.homologyMap_comp] at he
  exact congrArg (GlobalNaturality.globalSectionsToHypercohomology X (ReferenceSmooth.Integration.originalSmoothSingularComplexInt X) n)
    (ConcreteCategory.congr_hom he z)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.OrdinarySmoothGlobalUnits
