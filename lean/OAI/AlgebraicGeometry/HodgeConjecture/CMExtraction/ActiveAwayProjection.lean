import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedAwaySame
import OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

/-! # Active Away Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveAwayProjection.Approximation

noncomputable section

/-! Project the selected local factor and retain the actual restricted
product away from that factor. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] {d : F}
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
  {G : Type*} [Group G] [TopologicalSpace G]
  (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) →ₜ* G)

def finiteActiveProjection : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H →ₜ* G where
  toFun g := p (g v)
  map_one' := by change p 1 = 1; exact map_one p
  map_mul' g h := by change p (g v * h v) = _; exact map_mul p _ _
  continuous_toFun := p.continuous.comp (RestrictedProduct.continuous_eval v)

def activeAwayProjection : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H →ₜ*
    G × RestrictedAwaySame.Approximation.RestrictedAway (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr w)) v :=
  (finiteActiveProjection F H v p).prod (RestrictedAwaySame.Approximation.restrictedForgetPlaceContinuous _ v)

theorem activeAwayProjection_include (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v))) :
    activeAwayProjection F H v p
      (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr w)) v g) =
        (p g, 1) := by
  apply Prod.ext
  · exact congrArg p (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_same
      (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr w)) v g)
  · exact RestrictedAwaySame.Approximation.restrictedForgetPlace_include_same
      (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr w)) v g

theorem dense_diagonal_image_mem_closure {X A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    (r : X → A) (hr : DenseRange r) (f : A → B) (hf : Continuous f) (x : A) :
    f x ∈ closure (Set.range (fun y => f (r y))) := by
  have h := mem_closure_image hf.continuousAt (hr x)
  simpa only [← Set.range_comp, Function.comp_def] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveAwayProjection.Approximation
