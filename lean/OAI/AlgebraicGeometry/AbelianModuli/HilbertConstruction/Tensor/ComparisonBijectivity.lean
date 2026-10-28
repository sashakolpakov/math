import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Comparison Bijectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonBijectivity

noncomputable section

/-! A commuting square on pure tensors transports bijectivity through a source linear equivalence and a target additive equivalence. -/

universe u

theorem tensorComparison_bijective_of_pure_square
    {R B V V' W W' : Type u} [CommRing R]
    [AddCommGroup B] [Module R B] [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']
    [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (F : TensorProduct R B V →ₗ[R] W) (G : TensorProduct R B V' →ₗ[R] W')
    (e : V ≃ₗ[R] V') (ψ : W' →+ W) (hψ : Function.Bijective ψ) (hG : Function.Bijective G)
    (h : ∀ (b : B) (v : V), ψ (G (b ⊗ₜ[R] e v)) = F (b ⊗ₜ[R] v)) : Function.Bijective F := by
  let E := TensorProduct.congr (LinearEquiv.refl R B) e
  have hh : (F : TensorProduct R B V → W) = fun z => ψ (G (E z)) := by
    funext z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b v =>
      simpa only [E, TensorProduct.congr_tmul, LinearEquiv.refl_apply] using (h b v).symm
  rw [hh]
  exact hψ.comp (hG.comp E.bijective)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonBijectivity
