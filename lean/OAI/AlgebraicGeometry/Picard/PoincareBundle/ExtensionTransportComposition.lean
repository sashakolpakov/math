import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTwist
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionComposition

/-! # Extension Transport Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTransportComposition

noncomputable section

/-!
# Coefficient transport commutes with canonical composition of scalar extensions
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTwist OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionComposition

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  (f : R →+* A) (g : A →+* B) (g' : A →+* C)
  (e : B ≃+* C) (h : ∀ a, e (g a) = g' a) (M : ModuleCat.{u} R)

/-- Transporting after expansion into two scalar extensions equals expanding after transport. -/
theorem transport_composition_hom (z : (extendScalars (g.comp f)).obj M) :
    ExtensionTwist.extensionEquiv g g' e h ((extendScalars f).obj M)
        ((extendScalarsComp f g).hom.app M z) =
      (extendScalarsComp f g').hom.app M
        (ExtensionTwist.extensionEquiv (g.comp f) (g'.comp f) e (fun r => h (f r)) M z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      erw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b m =>
      exact (congrArg (ExtensionTwist.extensionEquiv g g' e h ((extendScalars f).obj M))
        (ExtensionComposition.composition_hom_tmul f g M b m)).trans
          (ExtensionComposition.composition_hom_tmul f g' M (e b) m).symm

/-- Transport also commutes with flattening the two scalar extensions. -/
theorem transport_composition_inv
    (z : (extendScalars g).obj ((extendScalars f).obj M)) :
    ExtensionTwist.extensionEquiv (g.comp f) (g'.comp f) e (fun r => h (f r)) M
        ((extendScalarsComp f g).inv.app M z) =
      (extendScalarsComp f g').inv.app M
        (ExtensionTwist.extensionEquiv g g' e h ((extendScalars f).obj M) z) := by
  apply ((extendScalarsComp f g').app M).toLinearEquiv.injective
  calc
    _ = ExtensionTwist.extensionEquiv g g' e h ((extendScalars f).obj M)
        ((extendScalarsComp f g).hom.app M ((extendScalarsComp f g).inv.app M z)) :=
      (transport_composition_hom f g g' e h M _).symm
    _ = ExtensionTwist.extensionEquiv g g' e h ((extendScalars f).obj M) z :=
      congrArg (ExtensionTwist.extensionEquiv g g' e h ((extendScalars f).obj M))
        (Iso.inv_hom_id_apply ((extendScalarsComp f g).app M) z)
    _ = _ := (Iso.inv_hom_id_apply ((extendScalarsComp f g').app M) _).symm

variable (f₁ f₂ : R →+* A)

/-- A module map extended to the final coefficient ring and flattened canonically. -/
def extendedMap (σ : (extendScalars f₁).obj M ⟶ (extendScalars f₂).obj M) :
    (extendScalars (g.comp f₁)).obj M ⟶ (extendScalars (g.comp f₂)).obj M :=
  (extendScalarsComp f₁ g).hom.app M ≫ (extendScalars g).map σ ≫
    (extendScalarsComp f₂ g).inv.app M

/-- Transport of the coefficient ring commutes with an actual extended module map. -/
theorem transport_extendedMap
    (σ : (extendScalars f₁).obj M ⟶ (extendScalars f₂).obj M)
    (z : (extendScalars (g.comp f₁)).obj M) :
    ExtensionTwist.extensionEquiv (g.comp f₂) (g'.comp f₂) e (fun r => h (f₂ r)) M
        (extendedMap g M f₁ f₂ σ z) =
      extendedMap g' M f₁ f₂ σ
        (ExtensionTwist.extensionEquiv (g.comp f₁) (g'.comp f₁) e (fun r => h (f₁ r)) M z) := by
  calc
    _ = (extendScalarsComp f₂ g').inv.app M
        (ExtensionTwist.extensionEquiv g g' e h ((extendScalars f₂).obj M)
          ((extendScalars g).map σ ((extendScalarsComp f₁ g).hom.app M z))) :=
      transport_composition_inv f₂ g g' e h M _
    _ = (extendScalarsComp f₂ g').inv.app M
        ((extendScalars g').map σ
          (ExtensionTwist.extensionEquiv g g' e h ((extendScalars f₁).obj M)
            ((extendScalarsComp f₁ g).hom.app M z))) :=
      congrArg ((extendScalarsComp f₂ g').inv.app M)
        (ExtensionTwist.extensionEquiv_naturality g g' e h σ _)
    _ = _ := congrArg (fun x => (extendScalarsComp f₂ g').inv.app M
      ((extendScalars g').map σ x)) (transport_composition_hom f₁ g g' e h M z)

/-- Place an extended map between specified, equal coordinate-ring homomorphisms. -/
def extendedMapTo (s₁ s₂ : R →+* B) (hs₁ : g.comp f₁ = s₁) (hs₂ : g.comp f₂ = s₂)
    (σ : (extendScalars f₁).obj M ⟶ (extendScalars f₂).obj M) :
    (extendScalars s₁).obj M ⟶ (extendScalars s₂).obj M :=
  eqToHom (congrArg (fun k => (extendScalars k).obj M) hs₁.symm) ≫
    extendedMap g M f₁ f₂ σ ≫
      eqToHom (congrArg (fun k => (extendScalars k).obj M) hs₂)

include h in
/-- Coefficient transport is compatible with the canonical identification of coordinate maps. -/
theorem transport_extendedMapTo (s₁ s₂ : R →+* B) (t₁ t₂ : R →+* C)
    (hs₁ : g.comp f₁ = s₁) (hs₂ : g.comp f₂ = s₂)
    (ht₁ : g'.comp f₁ = t₁) (ht₂ : g'.comp f₂ = t₂)
    (he₁ : ∀ r, e (s₁ r) = t₁ r) (he₂ : ∀ r, e (s₂ r) = t₂ r)
    (σ : (extendScalars f₁).obj M ⟶ (extendScalars f₂).obj M)
    (z : (extendScalars s₁).obj M) :
    ExtensionTwist.extensionEquiv s₂ t₂ e he₂ M (extendedMapTo g M f₁ f₂ s₁ s₂ hs₁ hs₂ σ z) =
      extendedMapTo g' M f₁ f₂ t₁ t₂ ht₁ ht₂ σ (ExtensionTwist.extensionEquiv s₁ t₁ e he₁ M z) := by
  subst s₁
  subst s₂
  subst t₁
  subst t₂
  simpa only [extendedMapTo, eqToHom_refl, Category.id_comp, Category.comp_id] using
    transport_extendedMap g g' e h M f₁ f₂ σ z

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTransportComposition
