import OAI.Geometry.ComplexBall.QuotientCompact

/-! # Compact Quotient Projection -/

namespace OAI.RepresentationTheory.Theta.Adelic.CompactQuotientProjection

noncomputable section

/-! Compactness of group quotients under a continuous surjective homomorphism. -/

variable {G J : Type*} [Group G] [Group J]

def mapCosets (Γ : Subgroup G) (f : G →* J) : G ⧸ Γ → J ⧸ Γ.map f :=
  Quotient.lift (fun g => QuotientGroup.mk (f g)) (by
    intro g h hgh
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    refine ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hgh, ?_⟩
    simp only [map_mul, map_inv])

theorem mapCosets_surjective (Γ : Subgroup G) (f : G →* J)
    (hf : Function.Surjective f) : Function.Surjective (mapCosets Γ f) := by
  intro y
  induction y using Quotient.inductionOn with
  | h y =>
    obtain ⟨g, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk g, rfl⟩

variable [TopologicalSpace G] [TopologicalSpace J]

theorem mapCosets_continuous (Γ : Subgroup G) (f : G →* J) (hf : Continuous f) :
    Continuous (mapCosets Γ f) :=
  (continuous_quotient_mk'.comp hf).quotient_lift _

theorem compact_cosets_map (Γ : Subgroup G) (f : G →* J)
    (hc : Continuous f) (hs : Function.Surjective f) [CompactSpace (G ⧸ Γ)] :
    CompactSpace (J ⧸ Γ.map f) := by
  constructor
  rw [← Set.range_eq_univ.mpr (mapCosets_surjective Γ f hs)]
  exact isCompact_range (mapCosets_continuous Γ f hc)

end

end OAI.RepresentationTheory.Theta.Adelic.CompactQuotientProjection
