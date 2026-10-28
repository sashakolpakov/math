import OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteSmoothGlobalUnit
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalFormMaps

/-! # Global Integration Classes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalIntegrationClasses

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

section

/-! # Genuine simplex integration on the original additive global complexes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
  (TopCat.of M)
local notation "F" => OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X
local notation "A" => forget₂ (ModuleCat ℂ) AddCommGrpCat
local notation "mapA" => Functor.mapHomologicalComplex (A) (ComplexShape.up ℕ)
local notation "mapF" => Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ)
local notation "ΓNat" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)
local notation "ΓInt" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℤ)
local notation "K" => Functor.obj
  (Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ))
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex Model M)
local notation "S" => Functor.obj
  (Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ))
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex Model M
  (ModuleCat.of ℂ ℂ))

/-- The actual smooth-global unit, with only complex module scalars forgotten. -/
def originalSmoothGlobalUnitNat :
    (mapA).obj (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains Model
      (ModuleCat.of ℂ ℂ) M) ⟶ (ΓNat).obj (S) :=
  (mapA).map (ConcreteSmoothGlobalUnit.actualSmoothCochainsToGlobalSheafSections Model M)

/-- Actual smooth-singular cochains on the original atlas, extended by zero. -/
def originalManifoldSmoothCochainsInt : CochainComplex AddCommGrpCat ℤ :=
  ((mapA).obj (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains Model
    (ModuleCat.of ℂ ℂ) M)).extend ComplexShape.embeddingUpNat

/-- Actual simplex integration, after scalar forgetting and extension by zero. -/
def originalManifoldSimplexIntegrationInt :
    ReferenceSmooth.GlobalForms.originalManifoldDeRhamComplexInt X ⟶ originalManifoldSmoothCochainsInt X :=
  HomologicalComplex.extendMap
    ((mapA).map (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap Model M))
      ComplexShape.embeddingUpNat

/-- The integer-indexed unit retains the canonical original global-section transports. -/
def originalSmoothGlobalUnitInt :
    originalManifoldSmoothCochainsInt X ⟶
      Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of M) (ReferenceSmooth.Integration.originalSmoothSingularComplexInt X) :=
  HomologicalComplex.extendMap (originalSmoothGlobalUnitNat X) ComplexShape.embeddingUpNat ≫
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (S) ComplexShape.embeddingUpNat).inv

/-- The full actual original global integration square in natural degrees. -/
theorem originalGlobalIntegrationNat_square :
    (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsNatIso X).inv ≫
        (ΓNat).map ((mapF).map (SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf Model M)) =
      (mapA).map (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap Model M) ≫
        originalSmoothGlobalUnitNat X := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext form
  simp only [HomologicalComplex.comp_f, AddCommGrpCat.comp_apply]
  exact SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf_globalValues Model M n form

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero retains the same original integration square in every integer degree. -/
theorem originalGlobalIntegrationInt_square :
    (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso X).inv ≫
        (ΓInt).map (ReferenceSmooth.Integration.originalSmoothIntegrationSheafComplexInt X) =
      originalManifoldSimplexIntegrationInt X ≫ originalSmoothGlobalUnitInt X := by
  apply (cancel_mono
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (S) ComplexShape.embeddingUpNat).hom).1
  simp only [ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso, Iso.trans_inv, Functor.mapIso_inv,
    ComplexShape.Embedding.extendFunctor_map, originalSmoothGlobalUnitInt,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality (Γ) (K)
    ComplexShape.embeddingUpNat ((mapF).map (SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf Model M))
  change HomologicalComplex.extendMap (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsNatIso X).inv
      ComplexShape.embeddingUpNat ≫
        ((Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (K) ComplexShape.embeddingUpNat).inv ≫
          ((ΓInt).map (HomologicalComplex.extendMap
            ((mapF).map (SmoothIntegrationGlobalValues.actualSmoothIntegrationSheaf Model M)) ComplexShape.embeddingUpNat) ≫
              (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (S) ComplexShape.embeddingUpNat).hom)) = _
  rw [hn, Iso.inv_hom_id_assoc, ← HomologicalComplex.extendMap_comp,
    originalGlobalIntegrationNat_square, HomologicalComplex.extendMap_comp]
  rfl

end

/-! # Actual original global holomorphic classes retain smooth integration in hypercohomology -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "ΓInt" => Functor.mapHomologicalComplex
  (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (ComplexShape.up ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- The unchanged original holomorphic global map commutes with actual integration and units. -/
theorem originalHolomorphicGlobalIntegrationInt_square :
    GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X ≫
        (originalManifoldSimplexIntegrationInt X ≫ originalSmoothGlobalUnitInt X) =
      (ΓInt).map (ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X) ≫
        (ΓInt).map (ReferenceSmooth.Integration.originalSmoothIntegrationSheafComplexInt X) := by
  have hn := congrArg (fun f => (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso X).hom ≫ f)
    (originalGlobalIntegrationInt_square X)
  have hg : (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso X).hom ≫
      (originalManifoldSimplexIntegrationInt X ≫ originalSmoothGlobalUnitInt X) =
    (ΓInt).map (ReferenceSmooth.Integration.originalSmoothIntegrationSheafComplexInt X) := by
    simpa only [Iso.hom_inv_id_assoc] using! hn.symm
  change ((ΓInt).map (ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X) ≫
    (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso X).hom) ≫ _ = _
  rw [Category.assoc, hg]

/-- The exact same integration square holds on original global cohomology. -/
theorem originalHolomorphicGlobalIntegration_homology_square (n : ℤ) :
    HomologicalComplex.homologyMap (GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) n ≫
        (HomologicalComplex.homologyMap (originalManifoldSimplexIntegrationInt X) n ≫
          HomologicalComplex.homologyMap (originalSmoothGlobalUnitInt X) n) =
      HomologicalComplex.homologyMap
        ((ΓInt).map (ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X)) n ≫
          HomologicalComplex.homologyMap
            ((ΓInt).map (ReferenceSmooth.Integration.originalSmoothIntegrationSheafComplexInt X)) n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, originalHolomorphicGlobalIntegrationInt_square]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Original de Rham global classes have their genuine integrated smooth-singular hyperclasses. -/
theorem originalHolomorphicGlobalIntegration_hyperClass (n : ℤ)
    (z : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X)).homology n) :
    ReferenceSmooth.Integration.originalSmoothIntegrationHypercohomologyAddEquiv X n
        (ReferenceSmooth.Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X n
          (GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) n z)) =
      GlobalNaturality.globalSectionsToHypercohomology X (ReferenceSmooth.Integration.originalSmoothSingularComplexInt X) n
        (HomologicalComplex.homologyMap (originalSmoothGlobalUnitInt X) n
          (HomologicalComplex.homologyMap (originalManifoldSimplexIntegrationInt X) n
            (HomologicalComplex.homologyMap (GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) n z))) := by
  rw [ReferenceSmooth.Hypercohomology.originalDeRhamSmoothHypercohomology_globalClass,
    ReferenceSmooth.Integration.originalSmoothIntegrationHypercohomologyAddEquiv_apply,
    ← GlobalNaturality.globalSectionsToHypercohomology_naturality]
  have he := ConcreteCategory.congr_hom
    (originalHolomorphicGlobalIntegration_homology_square X n) z
  have he' : HomologicalComplex.homologyMap
      ((ΓInt).map (ReferenceSmooth.Integration.originalSmoothIntegrationSheafComplexInt X)) n
        (HomologicalComplex.homologyMap
          ((ΓInt).map (ReferenceSmooth.Hypercohomology.originalHolomorphicToSmoothSheafComplexInt X)) n z) =
    HomologicalComplex.homologyMap (originalSmoothGlobalUnitInt X) n
      (HomologicalComplex.homologyMap (originalManifoldSimplexIntegrationInt X) n
        (HomologicalComplex.homologyMap (GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) n z)) := by
    simpa only [AddCommGrpCat.comp_apply] using! he.symm
  exact congrArg (GlobalNaturality.globalSectionsToHypercohomology X (ReferenceSmooth.Integration.originalSmoothSingularComplexInt X) n) he'

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalIntegrationClasses
