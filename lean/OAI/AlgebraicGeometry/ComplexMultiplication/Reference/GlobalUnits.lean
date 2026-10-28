import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceGlobalCohomology
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.OrdinarySmoothGlobalUnits
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSingularComparison

/-! # Global Units -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalUnits

noncomputable section

/-! # Original raw global units retain canonical integer transport -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
  (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
local notation "ΓNat" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)
local notation "ΓInt" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℤ)
local notation "O" => Functor.obj
  (Functor.mapHomologicalComplex (ReferenceSmooth.FormSheaf.originalSmoothFormSheafForget X) (ComplexShape.up ℕ))
    (AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
local notation "T" => OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℂ (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))
local notation "R" => OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℂ (TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X))

/-- Original raw cochains, extended by zero. -/
def originalRawSingularGlobalComplexInt : CochainComplex AddCommGrpCat ℤ :=
  (R).extend ComplexShape.embeddingUpNat

/-- The actual original raw-to-sheaf unit, transported canonically to integer degrees. -/
def originalRawSingularGlobalUnitInt :
    originalRawSingularGlobalComplexInt X ⟶
      Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ) :=
  HomologicalComplex.extendMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℂ Y)
      ComplexShape.embeddingUpNat ≫
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (T) ComplexShape.embeddingUpNat).inv

/-- The actual ambient-to-raw evaluation bridge, extended by zero. -/
def originalOrdinaryRawGlobalIntIso :
    OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X ≅ originalRawSingularGlobalComplexInt X :=
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
    (IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso ℂ Y)

omit [IsIntegral X.left] [Smooth X.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine global evaluation retains the same original unit in every integer degree. -/
theorem originalOrdinaryRawGlobalUnitInt_square :
    OrdinarySmoothGlobalUnits.originalOrdinaryGlobalUnitInt X ≫
        (ΓInt).map (SingularSmoothRestriction.originalOrdinarySingularComplexIntBridgeIso X).hom =
      (originalOrdinaryRawGlobalIntIso X).hom ≫ originalRawSingularGlobalUnitInt X := by
  apply (cancel_mono
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (T) ComplexShape.embeddingUpNat).hom).1
  simp only [OrdinarySmoothGlobalUnits.originalOrdinaryGlobalUnitInt, originalRawSingularGlobalUnitInt,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality (Γ) (O)
    ComplexShape.embeddingUpNat (SingularSheafBridge.originalComplexSingularSheafBridgeIso Y).hom
  change HomologicalComplex.extendMap (OrdinarySmoothGlobalUnits.originalOrdinaryGlobalUnitNat X)
      ComplexShape.embeddingUpNat ≫
        ((Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (O) ComplexShape.embeddingUpNat).inv ≫
          ((ΓInt).map (HomologicalComplex.extendMap
            (SingularSheafBridge.originalComplexSingularSheafBridgeIso Y).hom ComplexShape.embeddingUpNat) ≫
              (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (T)
                ComplexShape.embeddingUpNat).hom)) = _
  rw [hn, Iso.inv_hom_id_assoc, ← HomologicalComplex.extendMap_comp]
  change HomologicalComplex.extendMap
      ((Functor.mapHomologicalComplex (forget₂ (ModuleCat ℂ) AddCommGrpCat)
        (ComplexShape.up ℕ)).map
          (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) Y) ≫
        (IntrinsicReferenceGlobalCohomology.nativeSingularGlobalSheafBridgeIso ℂ Y).hom) ComplexShape.embeddingUpNat = _
  rw [IntrinsicReferenceGlobalCohomology.nativeOriginalSingularGlobalUnit_square, HomologicalComplex.extendMap_comp]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual integer-indexed raw unit retains the original natural-degree homology map. -/
theorem originalRawSingularGlobalUnitInt_homology_transport (n : ℕ) :
    HomologicalComplex.homologyMap (originalRawSingularGlobalUnitInt X) (n : ℤ) ≫
        (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℂ X n).hom =
      ((R).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom ≫
        HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℂ Y) n := by
  change HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℂ Y)
        ComplexShape.embeddingUpNat ≫
          (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (T) ComplexShape.embeddingUpNat).inv)
        (n : ℤ) ≫
      (HomologicalComplex.homologyMap
        (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (T) ComplexShape.embeddingUpNat).hom
        (n : ℤ) ≫ _) = _
  rw [HomologicalComplex.homologyMap_comp, Category.assoc,
    ← Category.assoc (HomologicalComplex.homologyMap
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ) (T) ComplexShape.embeddingUpNat).inv
      (n : ℤ)), ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]
  exact HomologicalComplex.extendHomologyIso_hom_naturality
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℂ Y) ComplexShape.embeddingUpNat
    (j := n) (hj' := rfl)

omit [IsIntegral X.left] [Smooth X.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- Actual ambient ordinary classes map to the same original raw singular hyperclasses. -/
theorem originalOrdinaryRawGlobalUnit_hyperClass (n : ℤ)
    (z : (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology n) :
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (SingularSmoothRestriction.originalOrdinarySingularComplexIntBridgeIso X).hom n
        (GlobalNaturality.globalSectionsToHypercohomology X (SingularSmoothRestriction.originalOrdinarySingularComplexInt X) n
          (HomologicalComplex.homologyMap (OrdinarySmoothGlobalUnits.originalOrdinaryGlobalUnitInt X) n z)) =
      GlobalNaturality.globalSectionsToHypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ) n
        (HomologicalComplex.homologyMap (originalRawSingularGlobalUnitInt X) n
          (HomologicalComplex.homologyMap (originalOrdinaryRawGlobalIntIso X).hom n z)) := by
  rw [← GlobalNaturality.globalSectionsToHypercohomology_naturality]
  have he := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (originalOrdinaryRawGlobalUnitInt_square X)
  simp only [HomologicalComplex.homologyMap_comp] at he
  exact congrArg (GlobalNaturality.globalSectionsToHypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ) n)
    (ConcreteCategory.congr_hom he z)

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The original natural-degree canonical resolution comparison is the actual raw integer unit. -/
theorem originalRawSingularGlobalUnit_hyperClass (n : ℕ)
    (z : (originalRawSingularGlobalComplexInt X).homology (n : ℤ)) :
    GlobalNaturality.globalSectionsToHypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ) (n : ℤ)
        (HomologicalComplex.homologyMap (originalRawSingularGlobalUnitInt X) (n : ℤ) z) =
      CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv ℂ X n
        (HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℂ Y) n
          (((R).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom z)) := by
  have hz := ConcreteCategory.congr_hom
    (originalRawSingularGlobalUnitInt_homology_transport X n) z
  have he : HomologicalComplex.homologyMap (originalRawSingularGlobalUnitInt X) (n : ℤ) z =
      (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℂ X n).inv
        (HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℂ Y) n
          (((R).extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom z)) := by
    apply (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℂ X n).addCommGroupIsoToAddEquiv.injective
    exact hz.trans (ConcreteCategory.congr_hom
      (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℂ X n).inv_hom_id _).symm
  exact congrArg (GlobalNaturality.globalSectionsToHypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ)
    (n : ℤ)) he

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalUnits
