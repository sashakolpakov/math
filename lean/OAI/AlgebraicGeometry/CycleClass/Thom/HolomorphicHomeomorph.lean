import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticLocalInverseAt
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Holomorphic Homeomorph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

noncomputable section

/-! A holomorphic homeomorphism with bijective differential has a holomorphic inverse; a holomorphic homeomorphism in both directions identifies model dimensions. -/

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticLocalInverseAt.Constructions

variable {M N E F : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω N]

theorem homeomorph_symm_analytic (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω e)
    (hd : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x)) :
    ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ω e.symm := by
  have hl : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F) ω e :=
    fun x => AnalyticLocalInverseAt.Constructions.isLocalDiffeomorphAt_of_bijective_mfderiv e x (he x) (hd x)
  let d := hl.diffeomorphOfBijective e.bijective
  have hi : (d.symm : N → M) = e.symm := by
    funext y
    apply e.injective
    change d (d.symm y) = e (e.symm y)
    simp only [Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  rw [← hi]
  exact d.symm.contMDiff

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω N] in
theorem homeomorph_mfderiv_bijective (e : M ≃ₜ N)
    (he : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) e)
    (hi : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E) e.symm) (x : M) :
    Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x) := by
  have hd : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) :=
    ⟨he.mdifferentiableOn, hi.mdifferentiableOn⟩
  exact hd.mfderiv_bijective (by trivial)

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω N] in
theorem homeomorph_model_finrank (e : M ≃ₜ N)
    (he : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) e)
    (hi : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E) e.symm) (x : M) :
    Module.finrank ℂ E = Module.finrank ℂ F :=
  (LinearEquiv.ofBijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x).toLinearMap
    (homeomorph_mfderiv_bijective e he hi x)).finrank_eq

end

end OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions
