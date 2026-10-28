import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleNormalFilling
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOrientationCoefficient

/-! # Normal Geometric Trace -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.NormalGeometricTrace

noncomputable section

section

/-!
# ChernClass: positive winding in the repaired complex normal orientation

The normal generator uses the relative boundary, radial projection,
ordered real coordinates, and circle Mayer–Vietoris. Following the positive
circle through those exact maps identifies the winding coefficient with
the actual ordered equator coordinate of the positive imaginary unit.
The repaired constructor makes that coordinate positive one.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def positiveCircleOrdinaryClass : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomology CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle 1 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) 1 CircleOrdinaryCycle.positiveCircleOrdinaryCycle

theorem positiveCircleOrdinaryClass_from_small :
    (CycleClass.Geometric.SphereHomologyInduction.Cycles.spherePoleHomologyComparison (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) 1).hom SmallCirclePositiveCycle.positiveCircleSmallClass =
      positiveCircleOrdinaryClass :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart)
    1 SmallCirclePositiveCycle.positiveCircleSmallCycle

theorem positiveCircleOrdinaryClass_coordinate :
    (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardCircleH1Iso.hom positiveCircleOrdinaryClass : ℝ) = CircleEquatorOrientation.chosenCircleEquatorSign := by
  rw [← positiveCircleOrdinaryClass_from_small]
  change (CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleH1Iso.hom
    ((CycleClass.Geometric.SphereHomologyInduction.Cycles.spherePoleHomologyComparison (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) 1).inv
      ((CycleClass.Geometric.SphereHomologyInduction.Cycles.spherePoleHomologyComparison (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) 1).hom SmallCirclePositiveCycle.positiveCircleSmallClass)) : ℝ) = _
  rw [Iso.hom_inv_id_apply]
  exact CircleOrientationCoefficient.positiveCircleSmallClass_coordinate

theorem normalPositiveCircleRelativeClass_realSphere :
    (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso 1 1 (by decide)).hom CircleNormalFilling.normalPositiveCircleRelativeClass =
      positiveCircleOrdinaryClass := by
  rw [CycleClass.Geometric.RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso_hom]
  change CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealSphereHomotopyEquiv 1).toFun) 1
    (CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (Fin 1 → ℂ))) 1
      (CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 1 CircleNormalFilling.normalPositiveCircleRelativeClass)) = _
  rw [CircleNormalFilling.normalPositiveCircleRelativeClass_boundary]
  have hc : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap CircleNormalMap.circleToNormalPunctured 1 positiveCircleOrdinaryClass =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of NormalWinding.windingNormalPunctured)) 1 CircleNormalFilling.normalPositiveCircleCycle :=
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map CircleNormalMap.circleToNormalPunctured) 1 CircleOrdinaryCycle.positiveCircleOrdinaryCycle
  rw [← hc]
  have hm : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap CircleNormalMap.circleToNormalPunctured 1 ≫
      CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (Fin 1 → ℂ))) 1 ≫
      CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealSphereHomotopyEquiv 1).toFun) 1 =
      𝟙 (CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomology CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle 1) := by
    simp only [CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, CircleNormalMap.circleToNormalPunctured_real_radial]
    rw [CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map_id, HomologicalComplex.homologyMap_id]
  exact ConcreteCategory.congr_hom hm positiveCircleOrdinaryClass

/-- The original integral normal coordinate of the positive loop filling
is precisely the original real equator basis coordinate. -/
theorem normalPositiveLoopCoefficient_eq_equatorSign :
    (PrimitiveNormalWinding.normalPositiveLoopCoefficient : ℝ) = CircleEquatorOrientation.chosenCircleEquatorSign := by
  change ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom PrimitiveNormalWinding.normalPositiveLoopRelativeClass : ℝ) = _
  rw [← CircleNormalFilling.normalPositiveCircleRelativeClass_eq_positiveLoop]
  change (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardCircleH1Iso.hom
    ((CycleClass.Geometric.RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso 1 1 (by decide)).hom CircleNormalFilling.normalPositiveCircleRelativeClass) : ℝ) = _
  rw [normalPositiveCircleRelativeClass_realSphere]
  exact positiveCircleOrdinaryClass_coordinate

/-- This computes the exact coefficient of the actual winding class in
the normal coordinate supplied by the repaired sphere constructor. -/
theorem normalWindingCoefficient_eq_equatorSign :
    (NormalWinding.normalWindingCoefficient : ℝ) = CircleEquatorOrientation.chosenCircleEquatorSign := by
  rw [← Positive.WindingNormalization.normalPositiveLoopCoefficient_cast, Rat.cast_intCast]
  exact normalPositiveLoopCoefficient_eq_equatorSign

theorem normalWindingCoefficient_eq_one_iff_equator_positive :
    NormalWinding.normalWindingCoefficient = 1 ↔ CircleEquatorOrientation.chosenCircleEquatorSign = 1 := by
  rw [← normalWindingCoefficient_eq_equatorSign]
  exact_mod_cast (Iff.rfl : NormalWinding.normalWindingCoefficient = 1 ↔ NormalWinding.normalWindingCoefficient = 1)

/-- The actual positive loop and the repaired geometric normal generator
agree, by the complete integral chain and Mayer–Vietoris calculation. -/
theorem normalWindingCoefficient_eq_one : NormalWinding.normalWindingCoefficient = 1 :=
  normalWindingCoefficient_eq_one_iff_equator_positive.mpr CircleEquatorOrientation.chosenCircleEquatorSign_eq_one

theorem normalPositiveLoopRelativeClass_eq_geometricGenerator :
    PrimitiveNormalWinding.normalPositiveLoopRelativeClass = (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1 :=
  (Positive.WindingNormalization.normalWindingCoefficient_eq_one_iff_positive_generator.mp normalWindingCoefficient_eq_one).symm

end

/-!
# ChernClass: the actual geometric trace of positive winding on the normal line

The compact fundamental class supported at the origin is the original
normal generator. Consequently the existing geometric trace of the actual
positive winding residue is the computed equator sign.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem complexCanonicalLocalClass_origin (d : ℕ) :
    CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (0 : Fin d → ℂ) =
      (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso d).inv 1 := by
  let e := chartAt (Fin d → ℂ) (0 : Fin d → ℂ)
  have he : ∀ u ∈ (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart e 0).source, CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart e 0 u = u := by
    intro u _
    simp only [CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_apply, e, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      id_eq, sub_zero]
  have hi : (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexChartLocalIso e 0 (mem_chart_source (Fin d → ℂ) 0) (2 * d)).hom = 𝟙 _ :=
    CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_eq_id (X := TopCat.of (Fin d → ℂ)) (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart e 0) 0
      (mem_chart_source (Fin d → ℂ) 0) he (2 * d)
  have hc := CycleClass.Geometric.ComplexChartOrientation.Cycles.complexChartLocalIso_canonical (p := d) (M := Fin d → ℂ) e (chart_mem_atlas (Fin d → ℂ) 0) 0
    (mem_chart_source (Fin d → ℂ) 0)
  rw [hi] at hc
  exact hc

theorem localHomologyToPoint_singleton (X : TopCat.{0}) (x : X) (n : ℕ) :
    CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint X {x} x (Set.mem_singleton x) n = 𝟙 (CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology X x n) := by
  change CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 X) _ n = _
  exact CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_id X ({x}ᶜ) n

theorem complexCompactFundamentalClass_origin (d : ℕ) :
    CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d ({0} : Set (Fin d → ℂ)) isCompact_singleton =
      (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso d).inv 1 := by
  have h := CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint d ({0} : Set (Fin d → ℂ))
    isCompact_singleton 0 (Set.mem_singleton 0)
  rw [localHomologyToPoint_singleton] at h
  exact h.trans (complexCanonicalLocalClass_origin d)

def normalOriginCompact : Compacts (Fin 1 → ℂ) := ⟨{0}, isCompact_singleton⟩

/-- The original winding residue, inserted into actual compact-support
cohomology using its singleton support. -/
def normalWindingCompactClass :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) NormalWinding.windingNormalLine 2 :=
  AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) NormalWinding.windingNormalLine normalOriginCompact 2
    NormalWinding.normalSupportedWindingClass

/-- The existing geometric trace of positive winding is exactly the
original primitive orientation coefficient. -/
theorem normalWindingCompactClass_geometricTrace :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace 1 (M := Fin 1 → ℂ) normalWindingCompactClass = NormalWinding.normalWindingCoefficient := by
  change AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace 1 (M := Fin 1 → ℂ)
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) NormalWinding.windingNormalLine normalOriginCompact (2 * 1)
      NormalWinding.normalSupportedWindingClass) = _
  rw [AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_stage_apply]
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 NormalWinding.normalSupportedWindingClass
    (CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass 1 ({0} : Set (Fin 1 → ℂ)) isCompact_singleton) = _
  rw [complexCompactFundamentalClass_origin, NormalWinding.normalSupportedWindingClass_eq_coefficient_smul, map_smul]
  change NormalWinding.normalWindingCoefficient * AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1) = _
  rw [AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.complexNormalRationalDualClass_integralEvaluation, mul_one]

theorem normalWindingCompactClass_geometricTrace_eq_one_iff :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace 1 (M := Fin 1 → ℂ) normalWindingCompactClass = 1 ↔
      CircleEquatorOrientation.chosenCircleEquatorSign = 1 := by
  rw [normalWindingCompactClass_geometricTrace, normalWindingCoefficient_eq_one_iff_equator_positive]

/-- Reconstructing the actual trace with the positive-loop generator
does give positive one on the same unchanged compact winding class. -/
theorem normalWindingCompactClass_positiveTrace :
    CycleClass.Geometric.TraceNormalization.Duality.complexManifoldTraceWithNormalization 1 Positive.WindingNormalization.positiveWindingModelNormalization
      (M := Fin 1 → ℂ) normalWindingCompactClass = 1 := by
  rw [Positive.WindingNormalization.positiveWindingTrace_eq_coefficient_smul]
  change NormalWinding.normalWindingCoefficient * AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace 1 (M := Fin 1 → ℂ) normalWindingCompactClass = 1
  rw [normalWindingCompactClass_geometricTrace]
  rcases PrimitiveNormalWinding.normalWindingCoefficient_eq_one_or_neg_one with h | h <;> rw [h] <;> norm_num

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.NormalGeometricTrace
