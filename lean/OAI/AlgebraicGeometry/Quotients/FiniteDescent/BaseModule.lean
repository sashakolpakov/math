import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic

/-! # Base Module -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseModule.Construction.BaseModuleSheaf

noncomputable section

/-! The actual base-linear module presheaf is a sheaf. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)

theorem isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X) (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget (ModuleCat.{u} Γ(S, ⊤)))]
  convert (Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat.{u})).mp
    (Scheme.Modules.isSheaf M) using 1
  all_goals rfl

def sheaf : TopCat.Sheaf (ModuleCat.{u} Γ(S, ⊤)) (Scheme.forgetToTop.obj X) :=
  ⟨SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M, BaseModuleSheaf.isSheaf π M⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseModule.Construction.BaseModuleSheaf
