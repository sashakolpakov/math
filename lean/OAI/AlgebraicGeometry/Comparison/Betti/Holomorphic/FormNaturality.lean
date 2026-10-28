import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Factorization
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainNaturality

/-! # Form Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormNaturality.Smooth

noncomputable section

/-! Naturality of the original holomorphic form realization for arbitrary compatible holomorphic evaluation maps. -/

open scoped _root_.Manifold ContDiff

variable {E F M N A B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [IsManifold 𝓘(ℝ, F) ∞ N] [IsManifold 𝓘(ℂ, F) ∞ N]
  [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

theorem holomorphicFormMap_naturality
    (φA : A →ₐ[ℂ] C(M, ℂ))
    (hA : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φA a))
    (hcA : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (φA a))
    (φB : B →ₐ[ℂ] C(N, ℂ))
    (hB : ∀ b, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℂ) ∞ (φB b))
    (hcB : ∀ b, ContMDiff 𝓘(ℂ, F) 𝓘(ℂ) ∞ (φB b))
    (f : B →ₐ[ℂ] A) (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (hcomm : ∀ b x, φA (f b) x = φB b (g x)) (n : ℕ) (a : Algebraic.Forms.Form B n) :
    Factorization.Smooth.holomorphicFormMap φA hA hcA n (Algebraic.Forms.pullback f n a) =
      HolomorphicPullback.pullback g hg n (Factorization.Smooth.holomorphicFormMap φB hB hcB n a) := by
  apply HolomorphicPullback.inclusion_injective n
  exact Smooth.CochainNaturality.smoothFormMap_naturality φA hA φB hB f g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) hcomm n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormNaturality.Smooth
