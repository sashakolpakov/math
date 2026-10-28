import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenCone
import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.InverseChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass

/-! # Open Normal Preimage -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenNormalPreimage.BundleCycles

noncomputable section

/-! An actual Chow preimage under graph normal extension restricts to the corresponding open graph preimage in every dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y X' Y' : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (g : X'.toOver ⟶ Y'.toOver)
    (a : X'.toOver ⟶ X.toOver) (b : Y'.toOver ⟶ Y.toOver)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] (h : a ≫ f = g ≫ b)

theorem graphNormalPointPreimage_open (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) (d : ℕ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap g) d
      (Chow.BundleCycles.graphNormalPointPullback g
        (Finsupp.comapDomain a.left (GraphNormal.InverseChow.BundleCycles.graphNormalPointPreimage f β) a.left.isOpenEmbedding.injective.injOn)) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap g) d
        (Finsupp.comapDomain (OpenCone.BundleCycles.graphOpenConeMap f g a b h) β
          (OpenCone.BundleCycles.graphOpenConeMap f g a b h).isOpenEmbedding.injective.injOn) := by
  let j := OpenCone.BundleCycles.graphOpenConeMap f g a b h
  let L := (DimensionChow.BundleCycles.dimensionChowTransport (OpenCone.BundleCycles.graphOpenConeMap_over f g a b h) d).comp
    (Open.ChowRestriction.BundleCycles.openChowRestriction j (Chow.BundleCycles.graphConeStructureMap f) d)
  have H := congrArg L (GraphNormal.InverseChow.BundleCycles.graphNormalPointPreimage_spec f β d)
  change DimensionChow.BundleCycles.dimensionChowTransport (OpenCone.BundleCycles.graphOpenConeMap_over f g a b h) d
    (Open.ChowRestriction.BundleCycles.openChowRestriction j (Chow.BundleCycles.graphConeStructureMap f) d
      (Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap f) d (Chow.BundleCycles.graphNormalPointPullback f (GraphNormal.InverseChow.BundleCycles.graphNormalPointPreimage f β)))) =
    DimensionChow.BundleCycles.dimensionChowTransport (OpenCone.BundleCycles.graphOpenConeMap_over f g a b h) d
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (Chow.BundleCycles.graphConeStructureMap f) d (Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap f) d β)) at H
  rw [Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass,
    Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle, Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle] at H
  exact (congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ (Chow.BundleCycles.graphConeStructureMap g) d)
    (OpenCone.BundleCycles.graphNormalPointPullback_open f g a b h (GraphNormal.InverseChow.BundleCycles.graphNormalPointPreimage f β))).symm.trans H

theorem graphNormalInverseChow_open_preimage (p : ℕ) (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) :
    GraphNormal.InverseChow.BundleCycles.graphNormalInverseChowValue g p
      (Finsupp.comapDomain (OpenCone.BundleCycles.graphOpenConeMap f g a b h) β
        (OpenCone.BundleCycles.graphOpenConeMap f g a b h).isOpenEmbedding.injective.injOn) =
      Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X' p
        (Finsupp.comapDomain a.left (GraphNormal.InverseChow.BundleCycles.graphNormalPointPreimage f β) a.left.isOpenEmbedding.injective.injOn) :=
  GraphNormal.InverseChow.BundleCycles.graphNormalInverseChowValue_eq_of_preimage g p _ _ (graphNormalPointPreimage_open f g a b h β)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenNormalPreimage.BundleCycles
