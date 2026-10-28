import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections

/-! # Base Global Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction

noncomputable section

/-! Restriction of literal global sections is linear over the actual base ring. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
universe u

def baseGlobalRestriction {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (V : X.Opens) :
    letI := BaseZeroSections.baseGlobalSectionsModule π M
    Γ(M, ⊤) →ₗ[Γ(S, ⊤)] (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op V) := by
  letI := BaseZeroSections.baseGlobalSectionsModule π M
  let a := (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op
  refine { toFun := M.presheaf.map a, map_add' := map_add _, map_smul' := ?_ }
  intro r x
  change M.presheaf.map a (π.appTop r • x) =
    X.presheaf.map ((initialOpOfTerminal isTerminalTop).to (op V)) (π.appTop r) •
      M.presheaf.map a x
  rw [M.map_smul]
  congr 2

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction
