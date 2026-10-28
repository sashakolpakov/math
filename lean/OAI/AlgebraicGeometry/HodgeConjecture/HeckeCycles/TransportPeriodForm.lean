import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover

/-! # Transport Period Form -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportPeriodForm.CM

noncomputable section

/-! Transport actual covector evaluations along equality of ball domains. -/

open scoped _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM

theorem evaluation {U V : TopologicalSpace.Opens GeometricSource.CM.BallChart} (h : U = V)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (c : V → X.analyticSpace)
    (α : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm X.analyticModel X.analyticSpace 1)
    (F : GeometricSource.CM.BallChart → GeometricSource.CM.BallChart → ℂ)
    (hα : ∀ (x : V) (ξ : GeometricSource.CM.BallChart), α (c x)
      (fun _ : Fin 1 => mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) c x ξ) = F x.val ξ) :
    ∀ (x : U) (ξ : GeometricSource.CM.BallChart), α (c (ReferenceCover.CM.transportPoint h x))
      (fun _ : Fin 1 => mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel)
        (c ∘ ReferenceCover.CM.transportPoint h) x ξ) = F x.val ξ := by
  subst V
  exact hα

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportPeriodForm.CM
