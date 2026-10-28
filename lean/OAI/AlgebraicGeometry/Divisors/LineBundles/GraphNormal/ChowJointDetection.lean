import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Conormal
import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.ChowJointDetection

/-! # Chow Joint Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ChowJointDetection.BundleCycles

noncomputable section

/-! Actual graph-normal fiber extension detects the source point-cycle
Chow classes jointly across all dimensions, with varying normal rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphNormalPointChow_joint_zero (z : X.carrier →₀ ℚ)
    (hz : ∀ e : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) e (Graph.Chow.BundleCycles.graphNormalPointPullback f z) = 0) :
    ∀ d : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d z = 0 := by
  have H := GlobalConormal.ChowJointDetection.BundleCycles.globalConormalPointChow_joint_zero (Graph.OpenAmbient.BundleCycles.graphFirstProjection f) (Graph.OpenAmbient.BundleCycles.graph f) (Graph.OpenAmbient.BundleCycles.graph_firstProjection f)
    (Graph.Conormal.BundleCycles.graphCenterStructureMap f) (Graph.Conormal.BundleCycles.graphConormalCenter_hasAffineSpaceCharts f)
    (Finsupp.mapDomain (Graph.OpenAmbient.BundleCycles.graph f).toImage z) (by
      intro e
      have H := congrArg (Closed.ChowOver.BundleCycles.schemeIsoChowEquiv (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f) (Graph.Chow.BundleCycles.graphConeStructureMap f)
        (Conormal.SupportCover.BundleCycles.globalConormalToSupport (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.Conormal.BundleCycles.graphCenterStructureMap f)
        (Graph.Conormal.BundleCycles.graphNormalConeEquiv_structure f) e) (hz e)
      rw [map_zero, Closed.ChowPointClass.BundleCycles.schemeIsoChowEquiv_pointClass] at H
      change Point.CycleChow.BundleCycles.pointCycleToChowQ (Conormal.SupportCover.BundleCycles.globalConormalToSupport (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.Conormal.BundleCycles.graphCenterStructureMap f) e
        (Finsupp.mapDomain (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).hom (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Graph.Chow.BundleCycles.graphNormalProjection f) z)) = 0 at H
      rw [Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality (Conormal.SupportCover.BundleCycles.globalConormalToSupport (Graph.OpenAmbient.BundleCycles.graph f).ker)
        (Graph.Chow.BundleCycles.graphNormalProjection f) (Graph.OpenAmbient.BundleCycles.graph f).toImage (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).hom
        (Graph.Conormal.BundleCycles.graphNormalConeEquiv_center_isPullback f)] at H
      exact H)
  intro d
  let e := asIso (Graph.OpenAmbient.BundleCycles.graph f).toImage
  have he : e.hom ≫ Graph.Conormal.BundleCycles.graphCenterStructureMap f = X.structureMap := Graph.Conormal.BundleCycles.graphToCenter_structure f
  apply (Closed.ChowOver.BundleCycles.schemeIsoChowEquiv e X.structureMap (Graph.Conormal.BundleCycles.graphCenterStructureMap f) he d).injective
  rw [map_zero]
  have HC := Closed.ChowPointClass.BundleCycles.schemeIsoChowEquiv_pointClass (f := Graph.Conormal.BundleCycles.graphCenterStructureMap f) (e := e)
    (g := X.structureMap) (h := he) d z
  exact HC.trans (H d)

theorem graphNormalPointChow_joint_equal (z w : X.carrier →₀ ℚ)
    (hzw : ∀ e : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) e (Graph.Chow.BundleCycles.graphNormalPointPullback f z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) e (Graph.Chow.BundleCycles.graphNormalPointPullback f w)) :
    ∀ d : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d z = Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d w := by
  have H := graphNormalPointChow_joint_zero f (z - w) (by
    intro e
    rw [map_sub, map_sub, hzw e, sub_self])
  intro d
  exact sub_eq_zero.mp ((map_sub (Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d) z w).symm.trans (H d))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ChowJointDetection.BundleCycles
