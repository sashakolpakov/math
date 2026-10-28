import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation

/-! # Intrinsic Graph Section -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass

noncomputable section

/-! The actual supported class of a base regular section on the graph
ambient becomes the literal first-projection pullback in product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left] (d : ℕ)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (s : Γ(Y.left, ⊤))

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU)
local notation "π" => OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection Y d
local notation "ι" => OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU
local notation "πU" => TopCat.prodFst (X := TopCat.of U) (Y := TopCat.of (Fin d → ℂ))
local notation "v₀" => OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s
local notation "vG" => OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s
local notation "vOld" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage F vG
local notation "vNew" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage πU (OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ι v₀)

def graphSectionClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U × (Fin d → ℂ))) (Set.range vOld)ᶜ 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) F (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo F vG) 2
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Affine.GraphSectionEquation.Constructions.graphSectionEquation Y d s)
      (Affine.GraphSectionEquation.Constructions.graphSectionEquation_mapsTo Y d s) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))

def baseSectionClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ι v₀))ᶜ 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) ι (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo ι v₀) 2
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s)
      (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))

theorem sectionSupportChange : Set.MapsTo (𝟙 (TopCat.of (U × (Fin d → ℂ)))) (Set.range vNew)ᶜ (Set.range vOld)ᶜ :=
  fun x hx hy => hx ((Set.ext_iff.mp (IntrinsicGraphEquationSupport.Constructions.Intrinsic.graphEquationSupport_range j d U hU v₀) x).mp hy)

theorem graphSectionClass_productPullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (U × (Fin d → ℂ))))
      (sectionSupportChange j d U hU s) 2 (graphSectionClass j d U hU s) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) πU
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo πU (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ι v₀)) 2 (baseSectionClass j U hU s) := by
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (U × (Fin d → ℂ)))) F
      (sectionSupportChange j d U hU s) (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo F vG) 2)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Affine.GraphSectionEquation.Constructions.graphSectionEquation Y d s)
      (Affine.GraphSectionEquation.Constructions.graphSectionEquation_mapsTo Y d s) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))
  have he := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) π (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo π v₀) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s) 2) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)
  have hn := IntrinsicGraphEquationSupport.Constructions.Intrinsic.graphClass_productPullback j d U hU v₀ 2
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y s)
      (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y s) 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))
  exact hc.trans ((congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) F
    (IntrinsicGraphEquationSupport.Constructions.Intrinsic.graphEquationSupport_mapsTo j d U hU v₀) 2) he.symm).trans hn)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass
