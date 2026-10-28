import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction

/-! # Base Top Section Equiv -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseTopSectionEquiv

noncomputable section

/-! The two actual base-ring actions on top sections are identified by
the canonical restriction map on the top open. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction

universe u

def baseTopSectionEquiv {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) :
    letI := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule f M
    Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op ⊤) := by
  letI := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule f M
  let a := SheafCohomology.Projective.BaseGlobalRestriction.baseGlobalRestriction f M ⊤
  have ha (s : Γ(M, ⊤)) : a s = s := by
    change M.presheaf.map (𝟙 (op ⊤)) s = s
    rw [M.presheaf.map_id]
    rfl
  exact LinearEquiv.ofBijective a ⟨fun x y h => (ha x).symm.trans (h.trans (ha y)),
    fun s => ⟨s, ha s⟩⟩

theorem baseTopSectionEquiv_apply {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (s : Γ(M, ⊤)) : baseTopSectionEquiv f M s = s := by
  change M.presheaf.map (𝟙 (op ⊤)) s = s
  rw [M.presheaf.map_id]
  rfl

theorem baseTopSectionEquiv_symm_apply {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op ⊤)) :
    (baseTopSectionEquiv f M).symm s = s := by
  have h := (baseTopSectionEquiv f M).apply_symm_apply s
  rwa [baseTopSectionEquiv_apply] at h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseTopSectionEquiv
