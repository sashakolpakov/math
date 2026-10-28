import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

/-! # Embedded Transport Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.EmbeddedTransportComposition

noncomputable section

/-! Embedded field-coordinate changes retain exact composition and
inverse formulas in each complex block. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

variable {E : Type} [Field E] [Algebra ℚ E]
    (u v : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) (τ : E →ₐ[ℚ] ℂ)

theorem embeddedLinearIso_trans_apply (z : Fin 3 → ℂ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (u.trans v) τ z = AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso v τ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso u τ z) := by
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso_apply, AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso_apply, AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso_apply]
  change (((LinearMap.toMatrix' (v.toLinearMap.comp u.toLinearMap)).map τ).mulVec z) = _
  rw [LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.mulVec_mulVec]

theorem embeddedLinearIso_refl_apply (z : Fin 3 → ℂ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (LinearEquiv.refl E (Fin 3 → E)) τ z = z := by
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso_apply]
  change (((LinearMap.toMatrix' (LinearMap.id : (Fin 3 → E) →ₗ[E] (Fin 3 → E))).map τ).mulVec z) = z
  simp

theorem embeddedLinearIso_inverse_apply (z : Fin 3 → ℂ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso u.symm τ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso u τ z) = z := by
  rw [← embeddedLinearIso_trans_apply]
  have he : u.trans u.symm = LinearEquiv.refl E (Fin 3 → E) := by
    apply LinearEquiv.ext
    intro a
    exact u.symm_apply_apply a
  rw [he, embeddedLinearIso_refl_apply]

end

end OAI.RepresentationTheory.Theta.Geometric.EmbeddedTransportComposition
