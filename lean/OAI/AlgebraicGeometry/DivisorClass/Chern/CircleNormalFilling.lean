import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOrdinaryCycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleNormalMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.WindingNormalization

/-! # Circle Normal Filling -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CircleNormalFilling

noncomputable section

/-! The positive two-arc circle gives the same actual normal relative class
as the original positive exponential loop. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def normalPositiveCircleCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of NormalWinding.windingNormalPunctured)) 1 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map CircleNormalMap.circleToNormalPunctured) 1 CircleOrdinaryCycle.positiveCircleOrdinaryCycle

theorem normalPositiveCircleCycle_winding :
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj (TopCat.of NormalWinding.windingNormalPunctured)) 1
      (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
        NormalWinding.normalPuncturedCoordinate_ne_zero) normalPositiveCircleCycle.val = (1 : ℚ) := by
  have h := LinearMap.congr_fun (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_pullback
    (TopCat.toSSet.map CircleNormalMap.circleToNormalPunctured) 1
    (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
      NormalWinding.normalPuncturedCoordinate_ne_zero)) CircleOrdinaryCycle.positiveCircleOrdinaryCycle.val
  have hn := WindingSingular.singularWindingCochain_naturality CircleNormalMap.circleToNormalPunctured
    NormalWinding.normalPuncturedCoordinate NormalWinding.normalPuncturedCoordinate_ne_zero
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) CircleNormalMap.circleToNormalPunctured).f 1
      (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
        NormalWinding.normalPuncturedCoordinate_ne_zero) =
    WindingSingular.singularWindingCochain CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CircleArcWinding.circleComplexCoordinate CircleArcWinding.circleComplexCoordinate_ne_zero at hn
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) 1
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) CircleNormalMap.circleToNormalPunctured).f 1
        (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
          NormalWinding.normalPuncturedCoordinate_ne_zero)) CircleOrdinaryCycle.positiveCircleOrdinaryCycle.val =
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj (TopCat.of NormalWinding.windingNormalPunctured)) 1
      (WindingSingular.singularWindingCochain (TopCat.of NormalWinding.windingNormalPunctured) NormalWinding.normalPuncturedCoordinate
        NormalWinding.normalPuncturedCoordinate_ne_zero) normalPositiveCircleCycle.val at h
  rw [hn] at h
  exact h.symm.trans CircleOrdinaryCycle.positiveCircleOrdinaryCycle_winding

theorem exists_normalPositiveCircleFilling :
    ∃ z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).X 2,
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).d 2 1 z =
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 1 normalPositiveCircleCycle.val := by
  let c := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 1 normalPositiveCircleCycle
  apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine) 1 c).mp
  exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero
    (CycleClass.Geometric.ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible NormalWinding.windingNormalLine 1 (by decide))) _ _

def normalPositiveCircleFilling : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).X 2 :=
  exists_normalPositiveCircleFilling.choose

theorem normalPositiveCircleFilling_boundary :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains NormalWinding.windingNormalLine).d 2 1 normalPositiveCircleFilling =
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 1 normalPositiveCircleCycle.val :=
  exists_normalPositiveCircleFilling.choose_spec

def normalPositiveCircleRelativeCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 2 :=
  ⟨(CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 2 normalPositiveCircleFilling,
    IntegralResidueEvaluation.integralRelativeProjection_cycle_of_boundary NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured
      normalPositiveCircleFilling normalPositiveCircleCycle.val normalPositiveCircleFilling_boundary⟩

def normalPositiveCircleRelativeClass : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 2 normalPositiveCircleRelativeCycle

theorem normalPositiveCircleRelativeClass_winding :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 NormalWinding.normalSupportedWindingClass
      normalPositiveCircleRelativeClass = 1 :=
  (IntegralResidueEvaluation.supportedWindingClass_integralBoundaryEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured
    NormalWinding.normalPuncturedCoordinate NormalWinding.normalPuncturedCoordinate_ne_zero normalPositiveCircleFilling
    normalPositiveCircleCycle.val normalPositiveCircleFilling_boundary).trans normalPositiveCircleCycle_winding

theorem normalWindingEvaluation_coordinate
    (x : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 NormalWinding.normalSupportedWindingClass x =
      ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom x : ℚ) * NormalWinding.normalWindingCoefficient := by
  have hx : x = ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom x) •
      (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1 := by
    apply (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).toLinearEquiv.injective
    change (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom x =
      (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom (_ • (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1)
    rw [map_zsmul, Iso.inv_hom_id_apply]
    exact (mul_one _).symm
  conv_lhs => rw [hx]
  rw [map_zsmul, NormalWinding.normalSupportedWindingClass_eq_coefficient_smul, map_smul]
  change ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom x : ℚ) *
    (NormalWinding.normalWindingCoefficient * AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2
      (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1)) = _
  rw [AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.complexNormalRationalDualClass_integralEvaluation]
  exact congrArg (fun r : ℚ => ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom x : ℚ) * r)
    (mul_one NormalWinding.normalWindingCoefficient)

theorem normalWindingEvaluation_injective : Function.Injective
    (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 NormalWinding.normalSupportedWindingClass) := by
  intro x y h
  rw [normalWindingEvaluation_coordinate, normalWindingEvaluation_coordinate] at h
  have hc := mul_right_cancel₀ NormalWinding.normalWindingCoefficient_ne_zero h
  apply (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).toLinearEquiv.injective
  exact_mod_cast hc

theorem normalPositiveCircleRelativeClass_eq_positiveLoop :
    normalPositiveCircleRelativeClass = PrimitiveNormalWinding.normalPositiveLoopRelativeClass := by
  apply normalWindingEvaluation_injective
  rw [normalPositiveCircleRelativeClass_winding, PrimitiveNormalWinding.normalPositiveLoopRelativeClass_winding]

theorem normalPositiveCircleRelativeClass_boundary :
    CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 1 normalPositiveCircleRelativeClass =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of NormalWinding.windingNormalPunctured)) 1 normalPositiveCircleCycle :=
  AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives.homologyConnecting_eq_of_lift (CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured)
    (CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_shortExact NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 1
    normalPositiveCircleRelativeCycle normalPositiveCircleFilling normalPositiveCircleCycle
    rfl normalPositiveCircleFilling_boundary.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CircleNormalFilling
