import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.VaryingPointPreimage
import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ChowJointDetection

/-! # Point Preimage -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.PointPreimage.BundleCycles

noncomputable section

/-! Every actual finite cycle on the graph normal cone admits a source
point-cycle preimage in all Chow grades, without a constant normal rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphNormalPointChow_preimage (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) :
    ∃ z : X.carrier →₀ ℚ, ∀ d : ℕ,
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d (Graph.Chow.BundleCycles.graphNormalPointPullback f z) =
        Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d β := by
  obtain ⟨z, hz⟩ := AffineBundle.VaryingPointPreimage.Cycles.affineBundlePointChow_preimage (Graph.Chow.BundleCycles.graphNormalProjection f) X.structureMap
    (Affine.SpaceChartBaseChange.BundleCycles.graphNormalCone_hasAffineSpaceCharts f) β
  refine ⟨z, ?_⟩
  intro d
  have H := congrArg (DimensionChow.BundleCycles.dimensionChowTransport (Graph.Chow.BundleCycles.graphConeStructureMap_normal f) d) (hz d)
  rw [Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle, Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle] at H
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Graph.Chow.BundleCycles.graphNormalProjection f) z) = _
  exact H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.PointPreimage.BundleCycles
