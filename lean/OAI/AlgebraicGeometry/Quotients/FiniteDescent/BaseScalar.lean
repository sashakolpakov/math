import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic

/-! # Base Scalar -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseScalar

noncomputable section

/-! Base-linear sections under composition of the structural morphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.BaseScalarRestriction

variable {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) (M : X.Modules)

def sectionsIso (U : X.Opens) :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ g) M).obj (op U) ≅
      (ModuleCat.restrictScalars g.appTop.hom).obj ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op U)) := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext x
  let x' : Γ(M, U) := x
  change X.presheaf.map U.leTop.op (f.appTop (g.appTop r)) • x' =
    X.presheaf.map U.leTop.op ((f ≫ g).appTop r) • x'
  rw [Scheme.Hom.comp_appTop]
  rfl

def presheafIso : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ g) M ≅
    SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M ⋙ ModuleCat.restrictScalars g.appTop.hom :=
  NatIso.ofComponents (fun U => sectionsIso f g M U.unop) (by
    intro U V h
    ext x
    rfl)

theorem sectionsIso_hom_apply (U : X.Opens)
    (x : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f ≫ g) M).obj (op U)) :
    (sectionsIso f g M U).hom x = x := rfl

end Construction.BaseScalarRestriction

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseScalar
