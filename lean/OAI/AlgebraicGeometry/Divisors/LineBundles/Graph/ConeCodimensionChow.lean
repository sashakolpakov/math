import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecializationCycleCodimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyConstantDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ComponentDimensionLocallyConstant
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRank

/-! # Cone Codimension Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ConeCodimensionChow.BundleCycles

noncomputable section

/-! Codimension selection on the actual graph normal cone preserves
Chow equality; its geometric dimension label is locally constant. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphConeComponentDimension (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker) : ℕ :=
  Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
    (X.componentVariety (X.supportComponent (irreducibleSetEquivPoints.symm (Chow.BundleCycles.graphNormalProjection f y)))).structureMap +
  AffineBundle.FiberRank.Cycles.affineBundleFiberRank (Chow.BundleCycles.graphNormalProjection f) X.structureMap (Chow.BundleCycles.graphNormalProjection f y)

theorem graphConeComponentDimension_locallyConstant : IsLocallyConstant (graphConeComponentDimension f) :=
  ((Projective.ComponentDimensionLocallyConstant.BundleCycles.projectivePointComponentDimension_locallyConstant X).comp_continuous (Chow.BundleCycles.graphNormalProjection f).continuous).comp₂
    ((AffineBundle.FiberRank.Cycles.affineBundleFiberRank_locallyConstant (Chow.BundleCycles.graphNormalProjection f) X.structureMap
      (Affine.SpaceChartBaseChange.BundleCycles.graphNormalCone_hasAffineSpaceCharts f)).comp_continuous (Chow.BundleCycles.graphNormalProjection f).continuous) (· + ·)

theorem graphConeCodimensionPart_chow_eq (p d : ℕ)
    (z w : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker →₀ ℚ)
    (hzw : Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap f) d z = Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap f) d w) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap f) d (SpecializationCycleCodimension.BundleCycles.graphConeCodimensionPart f p z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap f) d (SpecializationCycleCodimension.BundleCycles.graphConeCodimensionPart f p w) :=
  LocallyConstantDimension.BundleCycles.locallyConstantDimensionPart_chow_eq (Chow.BundleCycles.graphConeStructureMap f) d (graphConeComponentDimension f)
    (graphConeComponentDimension_locallyConstant f) p z w hzw

theorem graphNormal_genericPoint_codimension_iff (p : ℕ) (x : X.carrier) :
    SpecializationPointCodimension.BundleCycles.GraphConePointHasCodimension f p (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Chow.BundleCycles.graphNormalProjection f) x) ↔
      X.supportCodimension (irreducibleSetEquivPoints.symm x) = p := by
  have hd := AffineBundle.FiberRank.Cycles.affineBundleFiberGenericPoint_dimension_varying (Chow.BundleCycles.graphNormalProjection f) X.structureMap
    (Affine.SpaceChartBaseChange.BundleCycles.graphNormalCone_hasAffineSpaceCharts f) x
  rw [Chow.BundleCycles.graphConeStructureMap_normal] at hd
  have hc := Projective.PointComponentDimension.BundleCycles.projectiveSupport_dimension_add_codimension X (irreducibleSetEquivPoints.symm x)
  have he := congrArg (fun u : X.carrier =>
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety (X.supportComponent (irreducibleSetEquivPoints.symm u))).structureMap +
      AffineBundle.FiberRank.Cycles.affineBundleFiberRank (Chow.BundleCycles.graphNormalProjection f) X.structureMap u)
    (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection (Chow.BundleCycles.graphNormalProjection f) x)
  unfold SpecializationPointCodimension.BundleCycles.GraphConePointHasCodimension
  rw [he, hd]
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ConeCodimensionChow.BundleCycles
