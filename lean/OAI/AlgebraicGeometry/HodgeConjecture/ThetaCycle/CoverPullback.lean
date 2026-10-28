import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars
import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback

/-! # Cover Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverPullback.CM

noncomputable section

/-! ThetaCycle: pullback along the actual ball cover detects equality,
nonvanishing, and closedness of genuine forms on the principal surface. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  (f : M → N) (hs : Function.Surjective f)
  (hd : ∀ x, Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))

include hs hd

theorem raw_form_pullback_injective (n : ℕ) :
    Function.Injective (fun a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N n => a.pullback (E := E) f) := by
  intro a b hab
  funext y
  obtain ⟨x, rfl⟩ := hs y
  ext v
  choose u hu using (fun i : Fin n => hd x (v i))
  have h := congrArg (fun form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n => form x u) hab
  change a (f x) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x (u i)) =
    b (f x) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x (u i)) at h
  simpa only [hu] using h

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

theorem smooth_form_pullback_injective
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    Function.Injective (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (n := n) f hf) := by
  intro a b hab
  apply Subtype.ext
  apply raw_form_pullback_injective f hs hd n
  exact congrArg Subtype.val hab

theorem smooth_form_closed_iff_pullback
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 ↔ Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf a) = 0 := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback]
  exact (map_eq_zero_iff (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf)
    (smooth_form_pullback_injective f hs hd hf (n + 1))).symm

end General

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)

include hπ

theorem ball_cover_complex_smooth :
    ContMDiff 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℂ, X.analyticModel) ∞ π :=
  Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hπ.2.2.2.1

theorem ball_cover_real_derivative_bijective (z : B.Domain) :
    Function.Bijective (mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z) := by
  have he := ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_eq_complex_restrictScalars
    ((ball_cover_complex_smooth K B N X π hπ z).of_le (by simp))
  exact (congrArg (fun L : HeckeCycles.GeometricSource.CM.BallChart →L[ℝ] X.analyticModel => Function.Bijective L) he).mpr
    (hπ.2.2.2.2.1 z)

def ballCoverPullback (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain n :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback π (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (ball_cover_complex_smooth K B N X π hπ))

theorem ball_cover_pullback_injective (n : ℕ) :
    Function.Injective (ballCoverPullback K B N X π hπ n) :=
  smooth_form_pullback_injective π hπ.2.1
    (fun z => (ball_cover_real_derivative_bijective K B N X π hπ z).2) _ n

theorem ball_cover_closed_iff_pullback (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 ↔ Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ballCoverPullback K B N X π hπ n a) = 0 :=
  smooth_form_closed_iff_pullback π hπ.2.1
    (fun z => (ball_cover_real_derivative_bijective K B N X π hπ z).2) _ n a

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverPullback.CM
