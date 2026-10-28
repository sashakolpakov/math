import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection

/-! # Base Section Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionRestriction.Constructions.Class

noncomputable section

/-! The actual section class and its open-immersion inverse restrict
compatibly between nested ambient analytic opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U P : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (hPU : P ≤ U)
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hP : (P : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

local notation "i" => CategoryTheory.Functor.map (Opens.toTopCat (TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))) (homOfLE hPU)

 theorem baseOpenLift_restrict : i ≫ IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU = IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j P hP := by
  ext x : 1
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j).injective
  exact (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes j U hU ⟨x.val, hPU x.property⟩).trans (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes j P hP x).symm

variable (s : Γ(Y.left, ⊤))

 theorem baseSection_restriction_mapsTo : Set.MapsTo i
    (Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j P hP) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)))ᶜ
    (Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)))ᶜ := by
  intro x hx hy
  apply hx
  rw [ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range] at hy ⊢
  exact (congrArg (fun y => y ∈ Set.range (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s))
    (ConcreteCategory.congr_hom (baseOpenLift_restrict j U P hPU hU hP) x)).mp hy

 theorem baseSectionClass_restrict :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) i
      (baseSection_restriction_mapsTo j U P hPU hU hP s) 2 (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j P hP s := by
  let c := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s)
    (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) i (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU)
    (baseSection_restriction_mapsTo j U P hPU hU hP s)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)) 2
  have he := ThomOpenRestriction.Constructions.pairMap_congr (baseOpenLift_restrict j U P hPU hU hP)
    ((ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)).comp
      (baseSection_restriction_mapsTo j U P hPU hU hP s))
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j P hP) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)) 2
  exact (ConcreteCategory.congr_hom h c).trans (ConcreteCategory.congr_hom he c)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionRestriction.Constructions.Class
