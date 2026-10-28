import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingExt
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionClasses

/-! # Boundary Resolution -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.BoundaryResolution

noncomputable section

/-! Actual sheaf connecting classes evaluated on global sections in resolution coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

theorem sheafHZero_equiv_symm (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (t : F.obj.obj (op (⊤ : Opens X))) :
    (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).symm t =
      Ext.mk₀ ((ResolutionClasses.sheafHomGlobalEquiv F).symm t) := rfl

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
  (R : InjectiveResolution S.X₁)

def sheafConnectingResolutionSection (t : S.X₃.obj.obj (op (⊤ : Opens X))) :
    (R.cocomplex.X 1).obj.obj (op (⊤ : Opens X)) :=
  (ConnectingResolutionCocycle.connectingResolutionQuotient hS R).hom.app (op (⊤ : Opens X)) t

theorem sheafConnectingResolutionSection_closed (t : S.X₃.obj.obj (op (⊤ : Opens X))) :
    (R.cocomplex.d 1 2).hom.app (op (⊤ : Opens X)) (sheafConnectingResolutionSection hS R t) = 0 :=
  ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (⊤ : Opens X))) (ConnectingResolutionCocycle.connectingResolutionQuotient_closed hS R)) t

theorem sheafConnectingBoundary_resolution (t : S.X₃.obj.obj (op (⊤ : Opens X))) :
    ((CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm t).comp hS.extClass (zero_add 1) =
      -ResolutionClasses.sheafResolutionCycleClass R 1 (sheafConnectingResolutionSection hS R t)
        (sheafConnectingResolutionSection_closed hS R t) := by
  let := HasDerivedCategory.standard (TopCat.Sheaf AddCommGrpCat.{0} X)
  rw [sheafHZero_equiv_symm, ConnectingExt.connectingExtClass_eq_neg_resolution hS R, Ext.comp_neg,
    R.mk₀_comp_extMk]
  unfold ResolutionClasses.sheafResolutionCycleClass
  congr 2
  apply (ResolutionClasses.sheafHomGlobalEquiv (R.cocomplex.X 1)).injective
  rw [ResolutionClasses.sheafHomGlobalEquiv_naturality, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.BoundaryResolution
