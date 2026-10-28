import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Spec Global Section Identities -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecGlobalSectionIdentities

noncomputable section

/-! The canonical morphism to the spectrum of global functions preserves the native global coefficient action and section module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem schemeCoefficientMap_toSpecΓ (X : Scheme.{u}) :
    Coefficient.ModulePresheaf.schemeCoefficientMap X.toSpecΓ = RingHom.id Γ(X, ⊤) := by
  ext r
  change X.toSpecΓ.appTop ((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv r) = r
  rw [Scheme.toSpecΓ_appTop]
  exact (Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv_hom_id_apply r

def schemeGlobalSectionsToSpecIso {X : Scheme.{u}} (M : X.Modules) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.toSpecΓ).obj M ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) := by
  unfold Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor
  rw [schemeCoefficientMap_toSpecΓ]
  exact Global.ModuleSectionIdentity.globalModuleSectionsIdentity M

def moduleSpecΓPushforwardToSpecIso {X : Scheme.{u}} (M : X.Modules) :
    moduleSpecΓFunctor.obj ((pushforward X.toSpecΓ).obj M) ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) := by
  let c := (Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom
  have hc : X.toSpecΓ.appTop.hom.comp c = RingHom.id Γ(X, ⊤) :=
    schemeCoefficientMap_toSpecΓ X
  have e := Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv X.toSpecΓ c M ⊤
  rw [hc] at e
  exact e.trans (Global.ModuleSectionIdentity.globalModuleSectionsIdentity M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecGlobalSectionIdentities
