import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestriction

/-! # Top Restriction Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionNaturality.CechTopRestrictionNaturality

noncomputable section

/-! Top-section restriction is natural in the coefficient presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v z w
variable (C : Type u) [SemilatticeInf C] [OrderTop C]
  {A : Type v} [Category.{z} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C) {P Q : Cᵒᵖ ⥤ A} (τ : P ⟶ Q)

theorem map : TopRestriction.CechTopRestriction.map C U P ≫ ((cechComplexFunctor U).map τ).f 0 =
    τ.app (op ⊤) ≫ TopRestriction.CechTopRestriction.map C U Q := by
  change Pi.lift (fun t : Fin 1 → ι => P.map (homOfLE (le_top : (∏ᶜ (U ∘ t)) ≤ ⊤)).op) ≫
      Pi.lift (fun t : Fin 1 → ι => Pi.π (fun s : Fin 1 → ι => P.obj (op (∏ᶜ (U ∘ s)))) t ≫
        τ.app (op (∏ᶜ (U ∘ t)))) =
    τ.app (op ⊤) ≫ Pi.lift (fun t : Fin 1 → ι => Q.map (homOfLE (le_top : (∏ᶜ (U ∘ t)) ≤ ⊤)).op)
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
  exact τ.naturality _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TopRestrictionNaturality.CechTopRestrictionNaturality
