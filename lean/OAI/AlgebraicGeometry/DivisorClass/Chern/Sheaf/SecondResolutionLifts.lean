import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.BoundaryDegreeTwo
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle

/-! # Second Resolution Lifts -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf

noncomputable section

/-! Actual local lifts for the degree-two connecting resolution cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) {Y : TopCat.Sheaf AddCommGrpCat.{0} X} (R : InjectiveResolution Y)
  (f : S.X₁ ⟶ R.cocomplex.X 1) (hf : f ≫ R.cocomplex.d 1 2 = 0)
  {t : S.X₃.obj.obj (op (⊤ : Opens X))} (l : CohomologyLifts.SheafLocalLiftCover S.g t)

def CohomologyLifts.SheafLocalLiftCover.oneResolutionLift (i : X) : (R.cocomplex.X 1).obj.obj (op (l.domain i)) :=
  (ConnectingResolutionDegreeTwo.connectingResolutionOneMiddle hS R f).hom.app (op (l.domain i)) (l.section_ i)

theorem CohomologyLifts.SheafLocalLiftCover.oneResolutionLift_d (i : X) :
    (R.cocomplex.d 1 2).hom.app (op (l.domain i)) (l.oneResolutionLift hS R f i) =
      TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 2) le_top
        ((ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf).hom.app (op (⊤ : Opens X)) t) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun g => g.hom.app (op (l.domain i))) (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient_comm hS R f hf))
    (l.section_ i)
  change (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf).hom.app (op (l.domain i))
    (S.g.hom.app (op (l.domain i)) (l.section_ i)) =
      (R.cocomplex.d 1 2).hom.app (op (l.domain i)) (l.oneResolutionLift hS R f i) at h
  rw [l.image] at h
  exact h.symm.trans (TransitionCocycle.sheafSectionMap_restrict (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf) le_top t)

theorem CohomologyLifts.SheafLocalLiftCover.oneResolutionLift_transition (i j : X) :
    f.hom.app (op (l.domain i ⊓ l.domain j)) (l.transition hS i j) =
      TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 1) inf_le_right (l.oneResolutionLift hS R f j) -
        TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 1) inf_le_left (l.oneResolutionLift hS R f i) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun g => g.hom.app (op (l.domain i ⊓ l.domain j)))
      (ConnectingResolutionDegreeTwo.connectingResolutionOneMiddle_comm hS R f)) (l.transition hS i j)
  change (ConnectingResolutionDegreeTwo.connectingResolutionOneMiddle hS R f).hom.app (op (l.domain i ⊓ l.domain j))
    (S.f.hom.app (op (l.domain i ⊓ l.domain j)) (l.transition hS i j)) = _ at h
  rw [l.transition_map hS] at h
  refine h.symm.trans ?_
  change (ConnectingResolutionDegreeTwo.connectingResolutionOneMiddle hS R f).hom.app (op (l.domain i ⊓ l.domain j))
    (TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_right (l.section_ j) -
      TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_left (l.section_ i)) = _
  rw [map_sub, TransitionCocycle.sheafSectionMap_restrict, TransitionCocycle.sheafSectionMap_restrict]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf
