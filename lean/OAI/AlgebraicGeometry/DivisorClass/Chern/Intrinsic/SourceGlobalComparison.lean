import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SupportedResolutionComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SourceCohomology
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.CochainUnit
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap

/-! # Source Global Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SourceGlobalComparison

noncomputable section

/-! The native global Thom source model uses the same original relative source cochain comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (O : Opens X)

theorem supportedSectionsCochainInclusion_eq_native
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    Supported.CochainUnit.supportedSectionsCochainInclusion O ⊤ K = HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O ⊤ K := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl

theorem closedSourceSupportedSectionsIso_inv_inclusion :
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O ⊤).inv ≫
      HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) =
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) Y ((Opens.map f).obj O) ⊤ := by
  rw [← HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSourceSupportedSectionsIso_inclusion O ⊤ f, Iso.inv_hom_id_assoc]
  rfl

theorem relativeToSupportedSourceGlobalSections_native :
    Supported.SourceCohomology.relativeToSupportedSourceGlobalSections (ModuleCat.of ℚ ℚ) f O ≫
      (Supported.DerivedComparison.supportedSectionsFunctorIso O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)).hom =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) Y (((Opens.map f).obj O) : Set Y)).inv ≫
      HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections O ⊤ f := by
  apply (cancel_mono (Supported.CochainUnit.supportedSectionsCochainInclusion O ⊤
    (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f))).mp
  rw [Category.assoc, Supported.CochainUnit.supportedSectionsFunctorIso_inclusion,
    Supported.SourceCohomology.relativeToSupportedSourceGlobalSections_inclusion]
  rw [supportedSectionsCochainInclusion_eq_native]
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) Y (((Opens.map f).obj O) : Set Y) ≫
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) Y =
    ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) Y (((Opens.map f).obj O) : Set Y)).inv ≫
      (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) Y ((Opens.map f).obj O) ⊤ ≫
        (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O ⊤).inv)) ≫
      HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)
  rw [Category.assoc, Category.assoc, closedSourceSupportedSectionsIso_inv_inclusion,
    ← Category.assoc]
  exact (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections_inclusion (ModuleCat.of ℚ ℚ) Y ((Opens.map f).obj O)).symm

variable [MetrizableSpace Y]

theorem supportedSourceGlobalCohomologyIso_native (n : ℕ) :
    (Supported.SourceCohomology.supportedSourceGlobalCohomologyIso f O n).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
        (Supported.DerivedComparison.supportedSectionsFunctorIso O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)) =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) Y (((Opens.map f).obj O) : Set Y) n).symm ≪≫
      (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f O ⊤ n).symm := by
  have := Supported.SourceCohomology.relativeToSupportedSourceGlobalSections_quasiIso f O
  have hn : HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections O ⊤ f) n =
      (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f O ⊤ n).inv := by
    apply (cancel_mono (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f O ⊤ n).hom).mp
    rw [HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections_homology, Iso.inv_hom_id]
  apply Iso.ext
  change HomologicalComplex.homologyMap (Supported.SourceCohomology.relativeToSupportedSourceGlobalSections (ModuleCat.of ℚ ℚ) f O) n ≫
    HomologicalComplex.homologyMap
      (Supported.DerivedComparison.supportedSectionsFunctorIso O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)).hom n =
    HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) Y (((Opens.map f).obj O) : Set Y)).inv n ≫
      (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f O ⊤ n).inv
  rw [← hn, ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    relativeToSupportedSourceGlobalSections_native]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SourceGlobalComparison
