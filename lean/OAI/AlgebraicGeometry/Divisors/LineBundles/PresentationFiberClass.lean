import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationGradedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductGradedClass

/-! # Presentation Fiber Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationFiberClass.BundleCycles

noncomputable section

/-! The canonical class of the full actual integral-fiber pullback of a presentation cycle equals Betti pullback of its geometric class. Codimensions above the source dimension are handled by the absence of actual supports. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  {E : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom] [IsSeparated E.hom]
  [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
  (f : E ⟶ X.toOver) [Smooth f.left] [GeometricallyIntegral f.left]
  (charts : ∀ z : E.left, Open.ProductChart.BundleCycles.SchemeOpenProductChart f z) (e p : ℕ)
  (he : e + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom)

include charts in
theorem presentationFiberPointChow_class (z : X.RationalDimensionCycle p) :
    Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass E e p he
      (Point.CycleChow.BundleCycles.pointCycleToChowQ E.hom e (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension f.left (Chow.BundleCycles.pointCycle X p z))) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (X.geometricCycleClassMap p z) := by
  by_cases hp : p ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap
  · let d := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap - p
    have hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap := Nat.sub_add_cancel hp
    have h := LocallyProductGradedClass.BundleCycles.locallyProductFiberPointChow_class f charts d e p hd he (PresentationGradedCycle.BundleCycles.presentationGradedCycle X p d hd z)
    have hc := PresentationGradedCycle.BundleCycles.presentationGradedCycle_forget X p d hd z
    have hg := PresentationGradedClass.BundleCycles.presentationGradedCycle_class X p d hd z
    exact (congrArg (fun a => Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass E e p he
      (Point.CycleChow.BundleCycles.pointCycleToChowQ E.hom e (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension f.left a))) hc).symm.trans
        (h.trans (congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f) hg))
  · have hz : z = 0 := by
      ext Z
      have hd := PresentationComponentSupportClass.BundleCycles.integralPresentationSupport_dimension X p Z
      exact False.elim (hp (by omega))
    subst z
    rw [← Chow.BundleCycles.projectiveCyclePointMap_apply]
    simp only [map_zero]
    exact (congrArg (fun b => Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass E e p he (Point.CycleChow.BundleCycles.pointCycleToChowQ E.hom e b))
      (map_zero (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension f.left))).trans
        ((congrArg (Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass E e p he) (map_zero (Point.CycleChow.BundleCycles.pointCycleToChowQ E.hom e))).trans
          (map_zero (Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass E e p he)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationFiberClass.BundleCycles
