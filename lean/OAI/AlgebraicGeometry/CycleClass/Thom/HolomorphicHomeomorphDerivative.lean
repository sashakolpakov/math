import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Complex.Basic

/-! # Holomorphic Homeomorph Derivative -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorphDerivative.Constructions

noncomputable section

/-! The actual derivative of a holomorphic homeomorphism with holomorphic
inverse is injective, and actual injective differentials compose. -/

open scoped _root_.Manifold

variable {E F G M N P : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [TopologicalSpace P] [ChartedSpace G P]

theorem homeomorph_mfderiv_injective (e : M ≃ₜ N)
    (he : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) e)
    (hi : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E) e.symm) (x : M) :
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x) := by
  have h := mfderiv_comp x (hi (e x)) (he x)
  have hid : (e.symm ∘ e : M → M) = id := funext e.symm_apply_apply
  rw [hid, mfderiv_id] at h
  intro a b hab
  have hh := congrArg (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, E) e.symm (e x)) hab
  change ((mfderiv 𝓘(ℂ, F) 𝓘(ℂ, E) e.symm (e x)).comp (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x)) a =
    ((mfderiv 𝓘(ℂ, F) 𝓘(ℂ, E) e.symm (e x)).comp (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x)) b at hh
  rw [← h] at hh
  exact hh

include E F G in
theorem comp_mfderiv_injective (f : M → N) (g : N → P)
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f)
    (hg : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, G) g)
    (hfi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, F) 𝓘(ℂ, G) g x)) (x : M) :
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (g ∘ f) x) := by
  rw [mfderiv_comp x (hg (f x)) (hf x)]
  exact (hgi (f x)).comp (hfi x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorphDerivative.Constructions
