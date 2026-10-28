import OAI.AlgebraicGeometry.DivisorClass.Chern.SecondCechResolutionCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.RefinementGlobal

/-! # Second Cech Resolution Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original second resolution lifts and their two equations on a refined open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) {Y : TopCat.Sheaf AddCommGrpCat.{0} X} (R : InjectiveResolution Y)
  (f : S.X₁ ⟶ R.cocomplex.X 1) (hf : f ≫ R.cocomplex.d 1 2 = 0)
  {t : S.X₃.obj.obj (op (⊤ : Opens X))} (l : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g t)
  {J : Type} (V : J → Opens X) (r : J → X) (hr : ∀ j, V j ≤ l.domain (r j))

def Sheaf.CohomologyLifts.SheafLocalLiftCover.oneNativeResolutionRefinement : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex V R.cocomplex).X 1).X 0 :=
  (Cech.AbelianRefinement.nativeCechRefinement l.domain V r hr (R.cocomplex.X 1).obj).f 0 (l.oneNativeResolutionLift hS R f)

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.oneNativeResolutionRefinement_delta :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex V R.cocomplex).X 1).d 0 1 (l.oneNativeResolutionRefinement hS R f V r hr) =
      ((CategoryTheory.cechComplexFunctor V).map f.hom).f 1
        ((Abelian.CechCoordinates.abelianCechCoordinates S.X₁.obj V 1).symm
          (Cech.AbelianRefinement.abelianCechRefinementMap l.domain V r hr S.X₁.obj 1 (l.transitionCech hS))) := by
  change ((CategoryTheory.cechComplexFunctor V).obj (R.cocomplex.X 1).obj).d 0 1
    ((Cech.AbelianRefinement.nativeCechRefinement l.domain V r hr (R.cocomplex.X 1).obj).f 0
      (l.oneNativeResolutionLift hS R f)) = _
  rw [Cech.RefinementGlobal.nativeCechRefinement_d]
  have h := l.oneNativeResolutionLift_delta hS R f
  change ((CategoryTheory.cechComplexFunctor l.domain).obj (R.cocomplex.X 1).obj).d 0 1
    (l.oneNativeResolutionLift hS R f) = _ at h
  rw [h, Cech.RefinementGlobal.nativeCechRefinement_coefficient, Cech.RefinementGlobal.nativeCechRefinement_symm]

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.oneNativeResolutionRefinement_d :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex V R.cocomplex).d 1 2).f 0 (l.oneNativeResolutionRefinement hS R f V r hr) =
      FlasqueCechD.abelianCechHorizontalAugmentation V R.cocomplex 2
        ((GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 2
          ((ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf).hom.app (op (⊤ : Opens X)) t)) := by
  change ((CategoryTheory.cechComplexFunctor V).map (R.cocomplex.d 1 2).hom).f 0
    ((Cech.AbelianRefinement.nativeCechRefinement l.domain V r hr (R.cocomplex.X 1).obj).f 0
      (l.oneNativeResolutionLift hS R f)) = _
  rw [← Cech.RefinementGlobal.nativeCechRefinement_coefficient]
  have h := l.oneNativeResolutionLift_d hS R f hf
  change ((CategoryTheory.cechComplexFunctor l.domain).map (R.cocomplex.d 1 2).hom).f 0
    (l.oneNativeResolutionLift hS R f) = _ at h
  rw [h]
  exact ConcreteCategory.congr_hom (Cech.RefinementGlobal.nativeCechRefinement_global l.domain V r hr (R.cocomplex.X 2))
    ((GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 2
      ((ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf).hom.app (op (⊤ : Opens X)) t))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
