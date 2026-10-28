import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.DeformationOneBetti
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralGeometricFibers

/-! # Integral Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.IntegralDeformation.BundleCycles

noncomputable section

/-! For integral source and target presentations, the actual graph ambient scheme, deformation, and normal fiber are integral. Their native smooth structures are constructed for every original morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

instance graphConeOver_integral [IsIntegral X.carrier] : IsIntegral (Conormal.BundleCycles.graphConeOver f).left :=
  @GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker) X.carrier
    (Chow.BundleCycles.graphNormalProjection f) (Chow.BundleCycles.graphNormalProjection_geometricallyIntegral f)
    inferInstance inferInstance inferInstance inferInstance

instance graphConeOver_smooth : Smooth (Conormal.BundleCycles.graphConeOver f).hom := by
  change Smooth (Chow.BundleCycles.graphConeStructureMap f)
  rw [← Chow.BundleCycles.graphConeStructureMap_normal]
  infer_instance

instance graphAmbient_integral [IsIntegral X.carrier] [IsIntegral Y.carrier] : IsIntegral (OpenAmbient.BundleCycles.graphAmbient f) := by
  let : GeometricallyIntegral Y.structureMap := LineBundles.Smooth.IntegralGeometricFibers.BundleCycles.smoothIntegral_geometricallyIntegral_over_algClosed _
  let : GeometricallyIntegral (OpenAmbient.BundleCycles.graphFirstProjection f) :=
    inferInstanceAs (GeometricallyIntegral (Limits.pullback.fst (f.left ≫ Y.structureMap) Y.structureMap))
  exact @GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (OpenAmbient.BundleCycles.graphAmbient f) X.carrier
    (OpenAmbient.BundleCycles.graphFirstProjection f) inferInstance inferInstance inferInstance inferInstance inferInstance

instance graphAmbientOver_integral [IsIntegral X.carrier] [IsIntegral Y.carrier] :
    IsIntegral (Conormal.BundleCycles.graphAmbientOver f).left := graphAmbient_integral f

instance graphDeformationOver_integral [IsIntegral X.carrier] [IsIntegral Y.carrier] :
    IsIntegral (DeformationTopology.BundleCycles.graphDeformationOver f).left :=
  inferInstanceAs (IsIntegral (Global.Deformation.BundleCycles.globalDeformation (OpenAmbient.BundleCycles.graph f).ker))

instance graphSpecialFiberOver_closed : IsClosedImmersion (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f).left :=
  inferInstanceAs (IsClosedImmersion (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (OpenAmbient.BundleCycles.graph f).ker))

instance graphDeformationOver_noetherian : AlgebraicGeometry.IsNoetherian (DeformationTopology.BundleCycles.graphDeformationOver f).left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (Global.Deformation.BundleCycles.globalDeformation (OpenAmbient.BundleCycles.graph f).ker))

instance graphConeOver_noetherian : AlgebraicGeometry.IsNoetherian (Conormal.BundleCycles.graphConeOver f).left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.IntegralDeformation.BundleCycles
