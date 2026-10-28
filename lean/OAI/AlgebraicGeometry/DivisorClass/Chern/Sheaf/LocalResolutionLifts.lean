import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.BoundaryResolution
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle

/-! # Local Resolution Lifts -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf

noncomputable section

/-! Actual local lifts and their transition differences in an injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) (R : InjectiveResolution S.X₁)
  {t : S.X₃.obj.obj (op (⊤ : Opens X))} (l : CohomologyLifts.SheafLocalLiftCover S.g t)

def CohomologyLifts.SheafLocalLiftCover.resolutionLift (i : X) : (R.cocomplex.X 0).obj.obj (op (l.domain i)) :=
  (ConnectingResolutionCocycle.connectingResolutionMiddle hS R).hom.app (op (l.domain i)) (l.section_ i)

theorem CohomologyLifts.SheafLocalLiftCover.resolutionLift_d (i : X) :
    (R.cocomplex.d 0 1).hom.app (op (l.domain i)) (l.resolutionLift hS R i) =
      TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 1) le_top (BoundaryResolution.sheafConnectingResolutionSection hS R t) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (l.domain i))) (ConnectingResolutionCocycle.connectingResolutionQuotient_comm hS R))
    (l.section_ i)
  change (ConnectingResolutionCocycle.connectingResolutionQuotient hS R).hom.app (op (l.domain i))
      (S.g.hom.app (op (l.domain i)) (l.section_ i)) =
        (R.cocomplex.d 0 1).hom.app (op (l.domain i)) (l.resolutionLift hS R i) at h
  rw [l.image] at h
  exact h.symm.trans (TransitionCocycle.sheafSectionMap_restrict (ConnectingResolutionCocycle.connectingResolutionQuotient hS R) le_top t)

theorem CohomologyLifts.SheafLocalLiftCover.resolutionLift_transition (i j : X) :
    (R.ι.f 0).hom.app (op (l.domain i ⊓ l.domain j)) (l.transition hS i j) =
      TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 0) inf_le_right (l.resolutionLift hS R j) -
        TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 0) inf_le_left (l.resolutionLift hS R i) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (l.domain i ⊓ l.domain j)))
      (ConnectingResolutionCocycle.connectingResolutionMiddle_comm hS R)) (l.transition hS i j)
  change (ConnectingResolutionCocycle.connectingResolutionMiddle hS R).hom.app (op (l.domain i ⊓ l.domain j))
      (S.f.hom.app (op (l.domain i ⊓ l.domain j)) (l.transition hS i j)) = _ at h
  rw [l.transition_map hS] at h
  refine h.symm.trans ?_
  change (ConnectingResolutionCocycle.connectingResolutionMiddle hS R).hom.app (op (l.domain i ⊓ l.domain j))
    (TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_right (l.section_ j) -
      TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_left (l.section_ i)) = _
  rw [map_sub, TransitionCocycle.sheafSectionMap_restrict, TransitionCocycle.sheafSectionMap_restrict]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf
