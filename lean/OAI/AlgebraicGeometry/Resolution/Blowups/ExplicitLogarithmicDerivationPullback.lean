import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom
import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicFiltration

/-! # Explicit Logarithmic Derivation Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ExplicitLogarithmicDerivationPullback.Construction

noncomputable section

/-! Logarithmic normal derivations restrict through explicit étale maps and matching boundary ideals. -/

theorem extendEtaleRingDerivationHom_relative_logarithmic
    {k R S β : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (φ : R →ₐ[k] S) (hφ : φ.toRingHom.Etale) (w : β → R)
    (D : Derivation k R R) (hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) :
    Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k φ.toRingHom hφ φ.commutes D ∈
      Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun i => φ (w i)) := by
  intro i
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (hD i)
  change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k φ.toRingHom hφ φ.commutes D (φ.toRingHom (w i)) ∈
    Ideal.span {φ.toRingHom (w i)}
  rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hr, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem extendEtaleRingDerivationHom_logarithmic_of_ideal_eq
    {k R S β : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (φ : R →ₐ[k] S) (hφ : φ.toRingHom.Etale) (w : β → R) (v : β → S)
    (he : ∀ i, Ideal.span {φ (w i)} = Ideal.span {v i})
    (D : Derivation k R R) (hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) :
    Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k φ.toRingHom hφ φ.commutes D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k v := by
  rw [← LogarithmicFiltration.Construction.relativeLogarithmicDerivations_eq_of_principal_ideals (fun i => φ (w i)) v he]
  exact extendEtaleRingDerivationHom_relative_logarithmic φ hφ w D hD

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ExplicitLogarithmicDerivationPullback.Construction
