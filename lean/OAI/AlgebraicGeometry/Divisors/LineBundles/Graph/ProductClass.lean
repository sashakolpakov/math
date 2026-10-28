import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ProductOpenChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.PuncturedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentSupportClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.OpenProductChart

/-! # Product Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProductClass.BundleCycles

noncomputable section

/-! Actual global product charts for the graph ambient projection and actual affine-space charts for its normal projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphAmbient_isPullback :
    IsPullback (OpenAmbient.BundleCycles.graphFirstProjection f) (OpenAmbient.BundleCycles.graphSecondProjection f) X.structureMap Y.structureMap := by
  refine (IsPullback.of_hasPullback (f.left ≫ Y.structureMap) Y.structureMap).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp (OpenAmbient.BundleCycles.graphFirstProjection f)).symm)
    ((Category.comp_id _).trans (Category.id_comp (OpenAmbient.BundleCycles.graphSecondProjection f)).symm) ?_ (by simp)
  exact (Category.comp_id _).trans
    ((show f.left ≫ Y.structureMap = X.structureMap from f.w).trans (Category.id_comp X.structureMap).symm)

def graphAmbient_productIsLimit :
    IsLimit (BinaryFan.mk (Conormal.BundleCycles.graphFirstProjectionOver f) (Conormal.BundleCycles.graphSecondProjectionOver f)) :=
  BinaryFan.isLimitFlip (graphAmbient_isPullback f).flip.isLimit.pullbackConeEquivBinaryFanFunctor

instance graphSecondProjectionOver_smooth : Smooth (Conormal.BundleCycles.graphSecondProjectionOver f).left :=
  inferInstanceAs (Smooth (OpenAmbient.BundleCycles.graphSecondProjection f))

instance graphNormalProjectionOver_smooth : Smooth (Conormal.BundleCycles.graphNormalProjectionOver f).left :=
  inferInstanceAs (Smooth (Chow.BundleCycles.graphNormalProjection f))

instance graphNormalProjectionOver_integralFibers : GeometricallyIntegral (Conormal.BundleCycles.graphNormalProjectionOver f).left :=
  Chow.BundleCycles.graphNormalProjection_geometricallyIntegral f

instance graphSecondProjection_integralFibers [IsIntegral X.carrier] : GeometricallyIntegral (OpenAmbient.BundleCycles.graphSecondProjection f) := by
  have hf : f.left ≫ Y.structureMap = X.structureMap := f.w
  let : GeometricallyIntegral (f.left ≫ Y.structureMap) := hf.symm ▸
    LineBundles.Smooth.IntegralGeometricFibers.BundleCycles.smoothIntegral_geometricallyIntegral_over_algClosed X.structureMap
  exact inferInstanceAs (GeometricallyIntegral (pullback.snd (f.left ≫ Y.structureMap) Y.structureMap))

instance graphSecondProjectionOver_integralFibers [IsIntegral X.carrier] :
    GeometricallyIntegral (Conormal.BundleCycles.graphSecondProjectionOver f).left := graphSecondProjection_integralFibers f

def graphProjectionOpenProductChart [IsIntegral X.carrier] (z : (Conormal.BundleCycles.graphAmbientOver f).left) :
    Open.ProductChart.BundleCycles.SchemeOpenProductChart (Conormal.BundleCycles.graphSecondProjectionOver f) z :=
  Global.ProductOpenChart.BundleCycles.globalProductOpenChart X.toOver Y.toOver (Conormal.BundleCycles.graphAmbientOver f)
    (Conormal.BundleCycles.graphFirstProjectionOver f) (Conormal.BundleCycles.graphSecondProjectionOver f) (graphAmbient_productIsLimit f) z

def graphNormalOpenProductChart (z : (Conormal.BundleCycles.graphConeOver f).left) :
    Open.ProductChart.BundleCycles.SchemeOpenProductChart (Conormal.BundleCycles.graphNormalProjectionOver f) z :=
  AffineSpace.OpenProductChart.BundleCycles.affineBundleOpenProductChart (Conormal.BundleCycles.graphNormalProjectionOver f) (Affine.SpaceChartBaseChange.BundleCycles.graphNormalCone_hasAffineSpaceCharts f) z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProductClass.BundleCycles
