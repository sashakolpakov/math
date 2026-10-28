import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover

/-! # Section Puncture Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionPuncturePullback

noncomputable section

/-! A compatible section has the same punctured complement after
an injective change of ambient scheme and a surjective change of base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y T T₀ : Scheme.{u}}
  (f : Y ⟶ X) (r : T₀ ⟶ T) (s : T ⟶ X) (s₀ : T₀ ⟶ Y)
  (h : s₀ ≫ f = r ≫ s)

include h in
theorem range (hf : Function.Injective f) (hr : Function.Surjective r) (y : Y) :
    f y ∈ Set.range s ↔ y ∈ Set.range s₀ := by
  have he (t : T₀) : f (s₀ t) = s (r t) := by
    exact congrArg (fun g : T₀ ⟶ X => g t) h
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t₀, rfl⟩ := hr t
    exact ⟨t₀, hf ((he t₀).trans ht)⟩
  · rintro ⟨t₀, rfl⟩
    exact ⟨r t₀, (he t₀).symm⟩

include h in
theorem outside [IsClosedImmersion s] [IsClosedImmersion s₀]
    (hf : Function.Injective f) (hr : Function.Surjective r) :
    f ⁻¹ᵁ SectionIdealPuncturedCover.outside s.ker =
      SectionIdealPuncturedCover.outside s₀.ker := by
  ext y
  change f y ∉ (s.ker.support : Set X) ↔ y ∉ (s₀.ker.support : Set Y)
  rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker,
    s.isClosedEmbedding.isClosed_range.closure_eq,
    s₀.isClosedEmbedding.isClosed_range.closure_eq]
  exact not_congr (SectionPuncturePullback.range f r s s₀ h hf hr y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionPuncturePullback
