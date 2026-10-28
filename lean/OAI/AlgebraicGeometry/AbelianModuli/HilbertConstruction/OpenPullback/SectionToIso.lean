import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionToOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.OpenPullbackValues

/-! # Section To Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.SectionToIso

noncomputable section

/-! On an open immersion, pulling sections to the full inverse-image open is an isomorphism. In particular, sections on an open equal global sections of the canonical module pullback to that open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

theorem coefficientPullbackSectionToOpen_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (cY : R →+* Γ(Y, ⊤)) (cX : R →+* Γ(X, ⊤)) (hc : f.appTop.hom.comp cY = cX)
    (M : Y.Modules) (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U)
    (hU : U ≤ f.opensRange) (he : W = f ⁻¹ᵁ U) :
    IsIso (ModuleCat.ofHom (Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen f cY cX hc M U W hW)) := by
  subst cX
  have : IsIso (homOfLE hW) := by
    have h : homOfLE hW = (eqToIso he).hom := Subsingleton.elim _ _
    rw [h]
    infer_instance
  let e := Coefficient.OpenPullbackValues.coefficientOpenPullbackValueIso f cY M U hU
  have hmap : ModuleCat.ofHom
      (Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen f cY (f.appTop.hom.comp cY) rfl M U W hW) =
    e.hom ≫ (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp cY)
      ((Scheme.Modules.pullback f).obj M)).map (homOfLE hW).op := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  rw [hmap]
  infer_instance

def coefficientOpenGlobalSectionIso (c : R →+* Γ(Y, ⊤)) (M : Y.Modules) (U : Y.Opens) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op U) ≅
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (U.ι.appTop.hom.comp c) ((Scheme.Modules.pullback U.ι).obj M)).obj
        (op ⊤) :=
  Coefficient.OpenPullbackValues.coefficientOpenPullbackValueIso U.ι c M U (by rw [Scheme.Opens.opensRange_ι]) ≪≫
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (U.ι.appTop.hom.comp c) ((Scheme.Modules.pullback U.ι).obj M)).mapIso
      (eqToIso (congrArg op U.ι_preimage_self))

theorem coefficientOpenGlobalSectionIso_apply
    (c : R →+* Γ(Y, ⊤)) (M : Y.Modules) (U : Y.Opens)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op U)) :
    (coefficientOpenGlobalSectionIso c M U).hom x =
      ((Scheme.Modules.pullback U.ι).obj M).presheaf.map (homOfLE U.ι_preimage_self.ge).op
        (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).app U x) := by
  let N : U.toScheme.Modules := (Scheme.Modules.pullback U.ι).obj M
  let s : Γ(N, U.ι ⁻¹ᵁ U) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).app U x
  let k₁ : op (U.ι ⁻¹ᵁ U) ⟶ op (⊤ : U.toScheme.Opens) := eqToHom (congrArg op U.ι_preimage_self)
  let k₂ : op (U.ι ⁻¹ᵁ U) ⟶ op (⊤ : U.toScheme.Opens) := (homOfLE U.ι_preimage_self.ge).op
  change N.presheaf.map k₁ s = N.presheaf.map k₂ s
  exact ConcreteCategory.congr_hom (N.presheaf.congr_map (Subsingleton.elim k₁ k₂)) s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.SectionToIso
