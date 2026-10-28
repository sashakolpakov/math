import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorCoordinate
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Tensor Exterior -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorExterior.TensorExteriorAdditiveExt

noncomputable section

/-! # Additive maps from coordinate tensor forms are determined by exterior words -/

open scoped TensorProduct

universe u

variable (R σ M N : Type u) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  (n : ℕ) (f g : M ⊗[R] (⋀[R]^n (σ →₀ R)) →+ N)
  (h : ∀ (a : M) (v : Fin n → σ),
    f (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun j => Finsupp.single (v j) 1)) =
      g (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun j => Finsupp.single (v j) 1)))

include h in
theorem ext : f = g := by
  have hw (ω : ⋀[R]^n (σ →₀ R)) : ∀ a : M, f (a ⊗ₜ[R] ω) = g (a ⊗ₜ[R] ω) := by
    have hω : ω ∈ Submodule.span R (Set.range (fun v : Fin n → σ =>
        exteriorPower.ιMulti R n (fun j => Finsupp.single (v j) (1 : R)))) := by
      rw [ExteriorCoordinate.ExteriorCoordinateProjection.word_span]
      trivial
    induction hω using Submodule.span_induction with
    | mem ω hω =>
      obtain ⟨v, rfl⟩ := hω
      exact fun a => h a v
    | zero => intro a; simp only [TensorProduct.tmul_zero, map_zero]
    | add ω η hω hη ihω ihη =>
      intro a
      simp only [TensorProduct.tmul_add, map_add, ihω, ihη]
    | smul r ω hω ih =>
      intro a
      simpa only [TensorProduct.smul_tmul] using ih (r • a)
  apply AddMonoidHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a ω => exact hw ω a
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorExterior.TensorExteriorAdditiveExt
