import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingExtDegreeTwo
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.BoundaryResolution

/-! # Boundary Degree Two -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.BoundaryDegreeTwo

noncomputable section

/-! The actual degree-one sheaf connecting map evaluated in a degree-two injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) (R : InjectiveResolution S.X₁)

def sheafSecondConnectingQuotient :
    (CohomologyLifts.sheafInjectiveCokernelSequence S.X₃).X₃ ⟶ R.cocomplex.X 2 :=
  ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient (CohomologyLifts.sheafInjectiveCokernelSequence_shortExact S.X₃) R
    (ConnectingResolutionCocycle.connectingResolutionQuotient hS R) (ConnectingResolutionCocycle.connectingResolutionQuotient_closed hS R)

theorem sheafSecondConnectingQuotient_closed :
    sheafSecondConnectingQuotient hS R ≫ R.cocomplex.d 2 3 = 0 :=
  ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient_closed (CohomologyLifts.sheafInjectiveCokernelSequence_shortExact S.X₃) R
    (ConnectingResolutionCocycle.connectingResolutionQuotient hS R) (ConnectingResolutionCocycle.connectingResolutionQuotient_closed hS R)

def sheafSecondConnectingSection
    (t : (CohomologyLifts.sheafInjectiveCokernelSequence S.X₃).X₃.obj.obj (op (⊤ : Opens X))) :
    (R.cocomplex.X 2).obj.obj (op (⊤ : Opens X)) :=
  (sheafSecondConnectingQuotient hS R).hom.app (op (⊤ : Opens X)) t

theorem sheafSecondConnectingSection_closed
    (t : (CohomologyLifts.sheafInjectiveCokernelSequence S.X₃).X₃.obj.obj (op (⊤ : Opens X))) :
    (R.cocomplex.d 2 3).hom.app (op (⊤ : Opens X)) (sheafSecondConnectingSection hS R t) = 0 :=
  ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (⊤ : Opens X))) (sheafSecondConnectingQuotient_closed hS R)) t

theorem sheafConnectingBoundary_degreeTwo
    (t : (CohomologyLifts.sheafInjectiveCokernelSequence S.X₃).X₃.obj.obj (op (⊤ : Opens X))) :
    (CohomologyLifts.sheafInjectiveCokernelBoundary S.X₃ t).comp hS.extClass (show 1 + 1 = 2 from rfl) =
      -ResolutionClasses.sheafResolutionCycleClass R 2 (sheafSecondConnectingSection hS R t)
        (sheafSecondConnectingSection_closed hS R t) := by
  let := HasDerivedCategory.standard (TopCat.Sheaf AddCommGrpCat.{0} X)
  let T := CohomologyLifts.sheafInjectiveCokernelSequence S.X₃
  let hT := CohomologyLifts.sheafInjectiveCokernelSequence_shortExact S.X₃
  have hp := ConnectingExtDegreeTwo.connectingExt_comp_resolutionOne (C := TopCat.Sheaf AddCommGrpCat.{0} X)
    hT R (ConnectingResolutionCocycle.connectingResolutionQuotient hS R) (ConnectingResolutionCocycle.connectingResolutionQuotient_closed hS R)
  change (((CategoryTheory.Sheaf.H.equiv₀ T.X₃ isTerminalTop).symm t).comp hT.extClass
    (zero_add 1)).comp hS.extClass (show 1 + 1 = 2 from rfl) = _
  rw [BoundaryResolution.sheafHZero_equiv_symm, Ext.comp_assoc _ _ _ (zero_add 1)
      (show 1 + 1 = 2 from rfl) (show 0 + 1 + 1 = 2 from rfl),
    ConnectingExt.connectingExtClass_eq_neg_resolution hS R, Ext.comp_neg,
    hp, Ext.comp_neg, R.mk₀_comp_extMk]
  unfold ResolutionClasses.sheafResolutionCycleClass
  congr 2
  apply (ResolutionClasses.sheafHomGlobalEquiv (R.cocomplex.X 2)).injective
  rw [ResolutionClasses.sheafHomGlobalEquiv_naturality, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.BoundaryDegreeTwo
