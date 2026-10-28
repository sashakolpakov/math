import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Quotient.Construction.QuotientDescent

/-!
# Descent and comparison for effective quotients

An effective epimorphism with a specified kernel pair has the quotient
universal property. Two such quotients of the same relation are uniquely
isomorphic. These comparison isomorphisms supply transition maps for gluing.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] {R X Q : C} {s t : R ⟶ X}

/-- Maps equalizing the specified kernel pair descend uniquely along an
effective epimorphism. -/
theorem existsUnique_desc (q : X ⟶ Q) [EffectiveEpi q] (h : IsKernelPair q s t)
    {T : C} (f : X ⟶ T) (hf : s ≫ f = t ≫ f) :
    ∃! g : Q ⟶ T, q ≫ g = f := by
  have H : ∀ {Z : C} (a b : Z ⟶ X), a ≫ q = b ≫ q → a ≫ f = b ≫ f := by
    intro Z a b hab
    obtain ⟨l, rfl, rfl⟩ := h.exists_lift a b hab
    simpa only [Category.assoc] using congrArg (fun k : R ⟶ T => l ≫ k) hf
  exact ⟨EffectiveEpi.desc q f H, EffectiveEpi.fac q f H,
    fun g hg => EffectiveEpi.uniq q f H g hg⟩

/-- Two effective quotients with the same kernel relation have a unique
comparison isomorphism commuting with the quotient maps. -/
theorem existsUnique_iso {Q₁ Q₂ : C} (q₁ : X ⟶ Q₁) (q₂ : X ⟶ Q₂)
    [EffectiveEpi q₁] [EffectiveEpi q₂]
    (h₁ : IsKernelPair q₁ s t) (h₂ : IsKernelPair q₂ s t) :
    ∃! e : Q₁ ≅ Q₂, q₁ ≫ e.hom = q₂ := by
  obtain ⟨f, hf, _⟩ := existsUnique_desc q₁ h₁ q₂ h₂.w
  obtain ⟨g, hg, _⟩ := existsUnique_desc q₂ h₂ q₁ h₁.w
  have hfg : f ≫ g = 𝟙 Q₁ := by
    apply (cancel_epi q₁).mp
    rw [← Category.assoc, hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 Q₂ := by
    apply (cancel_epi q₂).mp
    rw [← Category.assoc, hg, hf, Category.comp_id]
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro e he
  apply Iso.ext
  exact (cancel_epi q₁).mp (he.trans hf.symm)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Quotient.Construction.QuotientDescent
