import OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionQuotient
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TwoStepBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.BoundaryResolution

/-! # Resolution Quotient Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionQuotientBoundary

noncomputable section

/-! The actual quotient boundary is minus the actual injective-resolution section class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X} (R : InjectiveResolution F)

def resolutionSecondQuotientSection
    (s : (cokernel (TwoStepQuotient.firstQuotientDifferential (ResolutionQuotient.resolutionZeroSequence R))).obj.obj (op (⊤ : Opens X))) :
    (R.cocomplex.X 2).obj.obj (op (⊤ : Opens X)) :=
  (ResolutionQuotient.resolutionSecondQuotientMap R).hom.app (op (⊤ : Opens X)) s

theorem resolutionSecondQuotientSection_closed
    (s : (cokernel (TwoStepQuotient.firstQuotientDifferential (ResolutionQuotient.resolutionZeroSequence R))).obj.obj (op (⊤ : Opens X))) :
    (R.cocomplex.d 2 3).hom.app (op (⊤ : Opens X)) (resolutionSecondQuotientSection R s) = 0 :=
  ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op (⊤ : Opens X))) (ResolutionQuotient.resolutionSecondQuotientMap_closed R)) s

theorem sheafTwoStepBoundary_resolution
    (s : (cokernel (TwoStepQuotient.firstQuotientDifferential (ResolutionQuotient.resolutionZeroSequence R))).obj.obj (op (⊤ : Opens X))) :
    TwoStepBoundary.sheafTwoStepBoundary (ResolutionQuotient.resolutionZeroSequence R) (ResolutionQuotient.resolutionZeroSequence_exact R) s =
      -ResolutionClasses.sheafResolutionCycleClass R 2 (resolutionSecondQuotientSection R s)
        (resolutionSecondQuotientSection_closed R s) := by
  change ((CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop).symm s).comp
    (TwoStepExt.twoStepQuotientExtClass (ResolutionQuotient.resolutionZeroSequence R) (ResolutionQuotient.resolutionZeroSequence_exact R)) (zero_add 2) = _
  rw [ResolutionQuotient.resolutionZeroSequence_twoStepExtClass, Ext.comp_neg, BoundaryResolution.sheafHZero_equiv_symm,
    R.mk₀_comp_extMk]
  unfold ResolutionClasses.sheafResolutionCycleClass
  congr 2
  apply (ResolutionClasses.sheafHomGlobalEquiv (R.cocomplex.X 2)).injective
  rw [ResolutionClasses.sheafHomGlobalEquiv_naturality, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

theorem sheafTwoStepBoundary_resolution_comparison
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.Exact) [Mono S.f]
    (R' : InjectiveResolution S.X₁) (φ : S ⟶ ResolutionQuotient.resolutionZeroSequence R') (hφ : φ.τ₁ = 𝟙 S.X₁)
    (s : (cokernel (TwoStepQuotient.firstQuotientDifferential S)).obj.obj (op (⊤ : Opens X))) :
    TwoStepBoundary.sheafTwoStepBoundary S hS s = -ResolutionClasses.sheafResolutionCycleClass R' 2
      (resolutionSecondQuotientSection R' ((TwoStepQuotientNaturality.secondQuotientMap φ).hom.app (op (⊤ : Opens X)) s))
      (resolutionSecondQuotientSection_closed R' _) := by
  have hn := TwoStepBoundary.sheafTwoStepBoundary_naturality hS (ResolutionQuotient.resolutionZeroSequence_exact R') φ s
  rw [hφ] at hn
  erw [CategoryTheory.Sheaf.H.map_id_apply] at hn
  exact hn.trans (sheafTwoStepBoundary_resolution R' _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionQuotientBoundary
