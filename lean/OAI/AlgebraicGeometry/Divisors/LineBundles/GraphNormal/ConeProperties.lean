import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.AffineSpaceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties

/-! # Cone Properties -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ConeProperties.BundleCycles

noncomputable section

/-! # LineBundleCycles: smoothness and integral fibers of the actual graph normal-cone projection -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

instance geometricallyIntegral_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@GeometricallyIntegral.{0}) := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (IsIntegral : ObjectProperty Scheme.{0}) :=
    ⟨fun e h => @IsIntegral.of_isIso _ _ h e.hom inferInstance⟩
  rw [GeometricallyIntegral.eq_geometrically]
  infer_instance

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

instance graphConormalProjection_smooth : Smooth (Global.GraphNormalCone.BundleCycles.graphConormalProjection f) := by
  have : IsZariskiLocalAtTarget (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact AffineSpace.ChartProperties.BundleCycles.morphismProperty_of_affineSpaceCharts (@Smooth) (Global.GraphNormalCone.BundleCycles.graphConormalProjection f)
    (Graph.AffineSpaceCharts.BundleCycles.graphConormal_exists_affineSpaceChart f) AffineSpace.ChartProperties.BundleCycles.affineSpaceSpecProjection_smooth

instance graphConormalProjection_geometricallyIntegral : GeometricallyIntegral (Global.GraphNormalCone.BundleCycles.graphConormalProjection f) :=
  AffineSpace.ChartProperties.BundleCycles.morphismProperty_of_affineSpaceCharts (@GeometricallyIntegral) (Global.GraphNormalCone.BundleCycles.graphConormalProjection f)
    (Graph.AffineSpaceCharts.BundleCycles.graphConormal_exists_affineSpaceChart f) (fun _ _ _ => inferInstance)

instance graphNormalConeProjection_smooth :
    Smooth (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f) := by
  have : IsZariskiLocalAtTarget (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact AffineSpace.ChartProperties.BundleCycles.morphismProperty_of_affineSpaceCharts (@Smooth)
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f)
    (Graph.AffineSpaceCharts.BundleCycles.graphNormalCone_exists_affineSpaceChart f) AffineSpace.ChartProperties.BundleCycles.affineSpaceSpecProjection_smooth

instance graphNormalConeProjection_geometricallyIntegral :
    GeometricallyIntegral (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f) :=
  AffineSpace.ChartProperties.BundleCycles.morphismProperty_of_affineSpaceCharts (@GeometricallyIntegral)
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (Graph.OpenAmbient.BundleCycles.graph f).ker ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f)
    (Graph.AffineSpaceCharts.BundleCycles.graphNormalCone_exists_affineSpaceChart f) (fun _ _ _ => inferInstance)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ConeProperties.BundleCycles
