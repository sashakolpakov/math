import OAI.RepresentationTheory.Theta.Geometric.EmbeddedTransportComposition
import OAI.RepresentationTheory.Theta.Geometric.Normalized.SubmoduleTransport

/-! # Embedded Normalized Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.EmbeddedNormalizedTransport

noncomputable section

/-! Equal subspaces in two field markings are identified by the exact
embedded change from the first marking to the second. -/

variable {E : Type} [Field E] [Algebra ℚ E]

theorem embeddedNormalizedSubmodule_transport
    (P Q : Submodule ℂ (Fin 3 → ℂ))
    (u v : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) (τ : E →ₐ[ℚ] ℂ)
    (h : P.comap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso u τ).toLinearMap =
      Q.comap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso v τ).toLinearMap) :
    P.map (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (u.symm.trans v) τ).toLinearMap = Q := by
  apply Normalized.SubmoduleTransport.normalizedSubmodule_transport P Q (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso u τ) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso v τ)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (u.symm.trans v) τ)
  · intro w
    rw [EmbeddedTransportComposition.embeddedLinearIso_trans_apply, EmbeddedTransportComposition.embeddedLinearIso_inverse_apply]
  · simpa only [Submodule.comap_equiv_eq_map_symm] using h

end

end OAI.RepresentationTheory.Theta.Geometric.EmbeddedNormalizedTransport
