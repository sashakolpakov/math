import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf

/-! # Restriction Coefficient Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCoefficientSections

noncomputable section

/-! Open restriction identifies actual section modules with image-open sections over any common coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Y) [IsOpenImmersion f]

theorem openImmersion_inverseApp_global (U : X.Opens) (s : Γ(Y, ⊤)) :
    (f.appIso U).inv (X.presheaf.map U.leTop.op (f.appTop s)) =
      Y.presheaf.map (f ''ᵁ U).leTop.op s := by
  have h := f.appLE_appIso_inv (U := (⊤ : Y.Opens)) (V := U)
    (show U ≤ f ⁻¹ᵁ ⊤ from le_top)
  exact ConcreteCategory.congr_hom h s

def coefficientOpenRestrictionSectionIso (c : R →+* Γ(Y, ⊤)) (M : Y.Modules) (U : X.Opens) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp c) (M.restrict f)).obj (op U) ≅
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op (f ''ᵁ U)) := by
  refine ModuleCat.isoMk (M.restrictAppIso f U) ?_
  intro r
  ext (x : Γ(M.restrict f, U))
  change Y.presheaf.map (f ''ᵁ U).leTop.op (c r) • (M.restrictAppIso f U).hom x =
    (M.restrictAppIso f U).hom (X.presheaf.map U.leTop.op (f.appTop (c r)) • x)
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, openImmersion_inverseApp_global]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCoefficientSections
