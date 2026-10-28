import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.PulledBackSupportSquare

/-! # Intrinsic Graph Equation Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic

noncomputable section

/-! An actual affine-base support and its supported class become the
literal first-projection pullbacks in the graph's product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport
open OAI.AlgebraicGeometry.CycleClass.Thom.PulledBackSupportSquare.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left] (d : ℕ)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU)
local notation "π" => OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection Y d
local notation "ι" => OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU
local notation "πU" => TopCat.prodFst (X := TopCat.of U) (Y := TopCat.of (Fin d → ℂ))

theorem graphEquationSupport_range :
    Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage F (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage π v)) =
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage πU (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ι v)) :=
  PulledBackSupportSquare.Constructions.pulledBackImage_square_range F π πU ι (IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection_coordinate_square d j U hU) v

theorem graphEquationSupport_mapsTo : Set.MapsTo F
    (Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage πU (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ι v)))ᶜ (Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage π v))ᶜ := by
  intro x hx
  apply ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo F (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage π v)
  rwa [graphEquationSupport_range j d U hU v]

theorem graphClass_productPullback (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range v)ᶜ n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) F (graphEquationSupport_mapsTo j d U hU v) n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) π (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo π v) n a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) πU (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo πU (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ι v)) n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) ι (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo ι v) n a) :=
  PulledBackSupportSquare.Constructions.relativePullback_square F π πU ι (IntrinsicGraphBaseProjection.Constructions.Intrinsic.graphBaseProjection_coordinate_square d j U hU)
    (graphEquationSupport_mapsTo j d U hU v) (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo π v)
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo πU (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage ι v)) (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo ι v) n a

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic
