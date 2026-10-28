import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections

/-! # Chart Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSections

noncomputable section

/-! The affine-chart section module is canonically the original module
of sections on that open, with the original ring action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

theorem image_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

theorem fromSpec_appLE :
    hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← (Spec Γ(X, U)).presheaf.map_comp]
  simp

theorem inverse_coefficient :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (hU.fromSpec.appIso ⊤).inv =
      X.presheaf.map (eqToHom (image_top U hU)).op := by
  rw [← fromSpec_appLE U hU]
  exact hU.fromSpec.appLE_appIso_inv hU.fromSpec_preimage_self.ge

def openIso (M : X.Modules) : Γ(M, U) ≅ Γ(M.restrict hU.fromSpec, ⊤) :=
  M.presheaf.mapIso (eqToIso (image_top U hU)).op

def fromSpecIso (M : X.Modules) :
    (ModuleExactSections.sections U).obj M ≅
      InternalHom.sections.obj (M.restrict hU.fromSpec) := by
  refine ModuleCat.isoMk (openIso U hU M) ?_
  intro r
  ext x
  let x' : Γ(M, U) := x
  change (hU.fromSpec.appIso ⊤).inv
    ((Spec Γ(X, U)).presheaf.map (𝟙 (op ⊤)) ((Scheme.ΓSpecIso Γ(X, U)).inv r)) •
      M.presheaf.map (eqToHom (image_top U hU)).op x' =
    M.presheaf.map (eqToHom (image_top U hU)).op (r • x')
  rw [(Spec Γ(X, U)).presheaf.map_id, CommRingCat.id_apply]
  exact (congrArg (fun t => t • M.presheaf.map (eqToHom (image_top U hU)).op x')
    (ConcreteCategory.congr_hom (inverse_coefficient U hU) r)).trans
      (M.val.map_smul (eqToHom (image_top U hU)).op r x').symm

def iso (M : X.Modules) :
    (ModuleExactSections.sections U).obj M ≅
      (AffineOpen.InternalHom.sections U hU).obj M :=
  fromSpecIso U hU M ≪≫ InternalHom.sections.mapIso
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app M)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSections
