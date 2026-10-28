import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.SupportSplitting
import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-! # Support Induction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.SupportInduction

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

open _root_.TopologicalSpace

theorem coherent_isZero_of_support_bot
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (h : (Annihilator.coherentAnnihilator M).support ≤ ⊥) : IsZero M := by
  apply (Module.VanishingOpen.moduleVanishingOpen_eq_top_iff M).mp
  apply top_unique
  intro x _
  by_contra hn
  exact h ((Annihilator.coherentAnnihilator_mem_support_iff M x).mpr hn)

theorem coherent_support_induction
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (P : ObjectProperty X.Modules) [P.IsClosedUnderExtensions]
    (hzero : ∀ M : X.Modules, IsZero M → P M)
    (hirred : ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
      (∀ (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType],
        (Annihilator.coherentAnnihilator M).support < Z → P M) →
      ∀ (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType],
        (Annihilator.coherentAnnihilator M).support ≤ Z → P M)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] : P M := by
  let : IsNoetherian X := ⟨⟩
  have hall (Z : Closeds X) : ∀ (N : X.Modules) [N.IsQuasicoherent] [N.IsFiniteType],
      (Annihilator.coherentAnnihilator N).support ≤ Z → P N := by
    apply (wellFounded_lt (α := Closeds X)).induction Z
    intro Z ih N _ _ hN
    rcases eq_or_ne Z ⊥ with rfl | hZ
    · exact hzero N (coherent_isZero_of_support_bot N hN)
    · by_cases hp : IsPreirreducible (Z : Set X)
      · exact hirred Z ⟨Closeds.coe_nonempty.mpr hZ, hp⟩
          (fun Q _ _ hQ => ih _ hQ Q le_rfl) N hN
      · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hp
        obtain ⟨z₁, z₂, hz₁, hz₂, hz, hn₁, hn₂⟩ := hp
        lift z₁ to Closeds X using hz₁
        lift z₂ to Closeds X using hz₂
        change ¬ Z ≤ z₁ at hn₁
        change ¬ Z ≤ z₂ at hn₂
        have hs : (Annihilator.coherentAnnihilator N).support ≤ (Z ⊓ z₁) ⊔ (Z ⊓ z₂) := by
          rw [← inf_sup_left]
          exact le_inf hN (hN.trans hz)
        obtain ⟨S, hS, hSN, hq₁, ht₁, hq₃, ht₃, h₁, h₃⟩ :=
          SupportSplitting.exists_coherent_support_split N (Z ⊓ z₁) (Z ⊓ z₂) hs
        let := hq₁
        let := ht₁
        let := hq₃
        let := ht₃
        rw [← hSN]
        exact P.prop_X₂_of_shortExact hS
          (ih _ (inf_lt_left.mpr hn₁) _ h₁)
          (ih _ (inf_lt_left.mpr hn₂) _ h₃)
  exact hall (Annihilator.coherentAnnihilator M).support M le_rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.SupportInduction
