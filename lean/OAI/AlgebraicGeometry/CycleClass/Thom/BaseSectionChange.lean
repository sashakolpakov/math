import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Base Section Change -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions.Equation

/-! The section class on an ambient open is the pullback of the original
normal-line class by the actual composite section equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (s : Γ(Y.left, ⊤))

def baseSectionEquation : TopCat.of U ⟶ PrincipalBoundary.Constructions.normalComplexLine := IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU ≫ GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s

theorem baseSectionEquation_mapsTo : Set.MapsTo (baseSectionEquation j U hU s)
    (Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)))ᶜ PrincipalBoundary.Constructions.puncturedComplexLine :=
  (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s).comp (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s))

theorem baseSectionClass_eq_equation : IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (baseSectionEquation j U hU s)
      (baseSectionEquation_mapsTo j U hU s) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) :=
  ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s))
    (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s) 2) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

end AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions.Equation

namespace AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions

/-! Changing an actual open scheme presentation of the base preserves
the section equation, its zero support, and its supported class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions.Equation OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y Z N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom] [IsIntegral N.left] [Smooth N.hom]
  (j : Y ⟶ N) (j' : Z ⟶ N) [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  (k : Z ⟶ Y) (hk : k ≫ j = j') (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hU' : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j'))

include hk in
theorem baseOpenLift_change (x : U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU' x) = IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x := by
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j).injective
  calc
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU' x)) =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k ≫ j) (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU' x) := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp k j _).symm
    _ = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j' (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU' x) :=
      congrArg (fun m => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map m (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU' x)) hk
    _ = x.val := IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes j' U hU' x
    _ = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x) := (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes j U hU x).symm

variable (s : Γ(Y.left, ⊤))

include hk in
theorem baseSectionEvaluation_change (x : U) :
    DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU' x) (k.left.appTop s) =
      DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x) s :=
  (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map k (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU' x) s).symm.trans
    (congrArg (fun y => DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation y s) (baseOpenLift_change j j' k hk U hU hU' x))

include hk in
theorem baseSectionEquation_change :
    Equation.baseSectionEquation j' U hU' (k.left.appTop s) = Equation.baseSectionEquation j U hU s := by
  ext x : 1
  funext i
  exact baseSectionEvaluation_change j j' k hk U hU hU' s x

include hk in
theorem baseSectionSupport_change :
    Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU') (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Z (k.left.appTop s))) =
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)) := by
  ext x
  rw [ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range, ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range, GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range, GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU' x) (k.left.appTop s) = 0 ↔
    DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x) s = 0
  exact (congrArg (fun z : ℂ => z = 0) (baseSectionEvaluation_change j j' k hk U hU hU' s x)).to_iff

include hk in
theorem baseSectionChange_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    (Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j' U hU') (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Z (k.left.appTop s))))ᶜ
    (Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)))ᶜ :=
  fun _ hx hy => hx ((baseSectionSupport_change j j' k hk U hU hU' s).symm ▸ hy)

theorem baseSectionClass_change :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (baseSectionChange_mapsTo j j' k hk U hU hU' s) 2 (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j' U hU' (k.left.appTop s) := by
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (Equation.baseSectionEquation j U hU s) (baseSectionChange_mapsTo j j' k hk U hU hU' s)
    (Equation.baseSectionEquation_mapsTo j U hU s) 2
  have h₂ := ThomOpenRestriction.Constructions.pairMap_congr ((Category.id_comp (Equation.baseSectionEquation j U hU s)).trans
      (baseSectionEquation_change j j' k hk U hU hU' s).symm)
    ((Equation.baseSectionEquation_mapsTo j U hU s).comp (baseSectionChange_mapsTo j j' k hk U hU hU' s))
    (Equation.baseSectionEquation_mapsTo j' U hU' (k.left.appTop s)) 2
  exact (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (baseSectionChange_mapsTo j j' k hk U hU hU' s) 2) (Equation.baseSectionClass_eq_equation j U hU s)).trans
    ((ConcreteCategory.congr_hom (h₁.trans h₂) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)).trans
      (Equation.baseSectionClass_eq_equation j' U hU' (k.left.appTop s)).symm)

end AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions

end

end OAI
