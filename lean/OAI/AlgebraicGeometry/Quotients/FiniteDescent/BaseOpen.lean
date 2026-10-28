import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionIs
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame

/-! # Base Open -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseOpen

noncomputable section

/-! Base-linear sections of an ambient open and of its open subscheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.BaseOpenSections

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)

def topIso : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) ≅
    (ModuleCat.restrictScalars π.appTop.hom).obj ((AffineSectionIs.Construction.AffineSectionAdjunction.sections X).obj M) := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext x
  let x' : Γ(M, ⊤) := x
  change π.appTop r • x' = X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op
    (π.appTop r) • x'
  rw [Subsingleton.elim (homOfLE le_rfl).op (𝟙 _), X.presheaf.map_id]
  rfl

def iso (U : X.Opens) :
    (ModuleCat.restrictScalars (U.ι ≫ π).appTop.hom).obj
      ((AffineSectionIs.Construction.AffineSectionAdjunction.sections U.toScheme).obj (M.restrict U.ι)) ≅
        (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U) :=
  (topIso (U.ι ≫ π) (M.restrict U.ι)).symm ≪≫
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafRestrictAppIso π U.ι M ⊤ ≪≫
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).mapIso (eqToIso U.ι_image_top.symm).op

theorem hom_apply (U : X.Opens) (s : Γ(M.restrict U.ι, ⊤)) :
    (iso π M U).hom s = (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom s := rfl

theorem inv_apply (U : X.Opens) (s : Γ(M, U)) :
    (iso π M U).inv s = (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).inv s := rfl

end Construction.BaseOpenSections

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseOpen
