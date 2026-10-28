import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ConeProperties
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ChowSpecialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiberFundamentalCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint

/-! # Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Chow.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual graph geometry and all dimension grades for the axiom-free specification -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

instance graphFirstProjection_isProper : IsProper (OpenAmbient.BundleCycles.graphFirstProjection f) := by
  have : IsProper Y.structureMap := Y.projective.isProper
  change IsProper (pullback.fst (f.left ≫ Y.structureMap) Y.structureMap)
  infer_instance

instance graphAmbient_isNoetherian : AlgebraicGeometry.IsNoetherian (OpenAmbient.BundleCycles.graphAmbient f) := by
  have : IsProper X.structureMap := X.projective.isProper
  exact Foundations.Scheme.ClosedProjective.isNoetherian_of_isProper_toSpec (OpenAmbient.BundleCycles.graphFirstProjection f ≫ X.structureMap)

def graphAmbientStructureMap : OpenAmbient.BundleCycles.graphAmbient f ⟶ Foundations.Scheme.ProjectiveSpace.complexBase := OpenAmbient.BundleCycles.graphSecondProjection f ≫ Y.structureMap

theorem graphAmbientStructureMap_first : OpenAmbient.BundleCycles.graphFirstProjection f ≫ X.structureMap = graphAmbientStructureMap f :=
  (congrArg (fun g => OpenAmbient.BundleCycles.graphFirstProjection f ≫ g) f.w).symm.trans
    (pullback.condition (f := f.left ≫ Y.structureMap) (g := Y.structureMap))

instance graphAmbientStructureMap_locallyOfFiniteType : LocallyOfFiniteType (graphAmbientStructureMap f) := by
  change LocallyOfFiniteType (OpenAmbient.BundleCycles.graphSecondProjection f ≫ Y.structureMap)
  infer_instance

def graphNormalProjection : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker ⟶ X.carrier :=
  Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphFirstProjection f

instance graphNormalProjection_geometricallyIntegral : GeometricallyIntegral (graphNormalProjection f) :=
  GraphNormal.ConeProperties.BundleCycles.graphNormalConeProjection_geometricallyIntegral f

def graphConeStructureMap : Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ graphAmbientStructureMap f

theorem graphConeStructureMap_normal : graphNormalProjection f ≫ X.structureMap = graphConeStructureMap f := by
  change (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphFirstProjection f) ≫ X.structureMap = _
  rw [Category.assoc, graphAmbientStructureMap_first]
  rfl

def graphProjectionPointPullback : (Y.carrier →₀ ℚ) →ₗ[ℚ] (OpenAmbient.BundleCycles.graphAmbient f →₀ ℚ) :=
  FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback (OpenAmbient.BundleCycles.graphSecondProjection f)

def graphNormalPointPullback : (X.carrier →₀ ℚ) →ₗ[ℚ] (Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) :=
  Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (graphNormalProjection f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Chow.BundleCycles
