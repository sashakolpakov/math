import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom

/-! # Mapped Dual Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MappedDualFrame.Construction

noncomputable section

/-! Transport exact dual coordinate frames through a specified étale algebra map. -/

universe u v

variable (k : Type u) {R S : Type u} {ι : Type v} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [DecidableEq ι]

theorem etale_mapped_dual_frame (f : R →ₐ[k] S) (hf : f.toRingHom.Etale)
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0) (i j : ι) :
    Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes (D i) (f (g j)) =
      if i = j then 1 else 0 := by
  have h : Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes (D i) (f (g j)) =
      f (D i (g j)) :=
    Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply k f.toRingHom hf f.commutes (D i) (g j)
  rw [h, hD]
  split_ifs <;> simp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MappedDualFrame.Construction
