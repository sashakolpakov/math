import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.SecondResolutionLifts
import OAI.AlgebraicGeometry.DivisorClass.Chern.TransitionIntrinsicResolution

/-! # Second Cech Resolution Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original second local lifts as actual native Cech cochains in resolution degree one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) {Y : TopCat.Sheaf AddCommGrpCat.{0} X} (R : InjectiveResolution Y)
  (f : S.X₁ ⟶ R.cocomplex.X 1) (hf : f ≫ R.cocomplex.d 1 2 = 0)
  {t : S.X₃.obj.obj (op (⊤ : Opens X))} (l : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g t)

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.oneResolutionCech_delta :
    Abelian.CechClasses.abelianCechCoefficient (X := X) l.domain f.hom 1 (l.transitionCech hS) =
      Abelian.CechCoordinates.abelianCechDelta (R.cocomplex.X 1).obj l.domain 0
        (Cech.LocalSections.abelianCechLocalSections l.domain (R.cocomplex.X 1) (l.oneResolutionLift hS R f)) := by
  funext a
  change f.hom.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain a))
    (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ _ (l.transition hS (a 0) (a 1))) = _
  have h := Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict f
    (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 1))
    (l.transition hS (a 0) (a 1))
  refine h.trans ?_
  refine (congrArg (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 1)
    (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 1)))
    (l.oneResolutionLift_transition hS R f (a 0) (a 1))).trans ?_
  rw [map_sub, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp, Cech.LocalSections.abelianCechLocalSections_delta]

def Sheaf.CohomologyLifts.SheafLocalLiftCover.oneNativeResolutionLift : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex l.domain R.cocomplex).X 1).X 0 :=
  (Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj l.domain 0).symm
    (Cech.LocalSections.abelianCechLocalSections l.domain (R.cocomplex.X 1) (l.oneResolutionLift hS R f))

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.oneNativeResolutionLift_delta :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex l.domain R.cocomplex).X 1).d 0 1 (l.oneNativeResolutionLift hS R f) =
      ((CategoryTheory.cechComplexFunctor l.domain).map f.hom).f 1
        ((Abelian.CechCoordinates.abelianCechCoordinates S.X₁.obj l.domain 1).symm (l.transitionCech hS)) := by
  change ((CategoryTheory.cechComplexFunctor l.domain).obj (R.cocomplex.X 1).obj).d 0 1
    ((Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj l.domain 0).symm
      (Cech.LocalSections.abelianCechLocalSections l.domain (R.cocomplex.X 1) (l.oneResolutionLift hS R f))) = _
  rw [Cech.IntrinsicOperators.abelianCechCoordinates_symm_d]
  have he := Cech.IntrinsicOperators.abelianCechCoordinates_symm_coefficient (F := S.X₁.obj)
    (G := (R.cocomplex.X 1).obj) l.domain f.hom 1 (l.transitionCech hS)
  exact (congrArg (Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj l.domain 1).symm
    (l.oneResolutionCech_delta hS R f).symm).trans he.symm

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.oneNativeResolutionLift_d :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex l.domain R.cocomplex).d 1 2).f 0 (l.oneNativeResolutionLift hS R f) =
      FlasqueCechD.abelianCechHorizontalAugmentation l.domain R.cocomplex 2
        ((GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 2
          ((ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf).hom.app (op (⊤ : Opens X)) t)) := by
  apply (Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 2).obj l.domain 0).injective
  funext a
  change Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 2).obj l.domain 0
      (((CategoryTheory.cechComplexFunctor l.domain).map (R.cocomplex.d 1 2).hom).f 0
        ((Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj l.domain 0).symm
          (Cech.LocalSections.abelianCechLocalSections l.domain (R.cocomplex.X 1) (l.oneResolutionLift hS R f)))) a = _
  rw [Abelian.CechCoordinates.abelianCechCoordinates_naturality, AddEquiv.apply_symm_apply]
  change (R.cocomplex.d 1 2).hom.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain a))
    (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 0)
      (l.oneResolutionLift hS R f (a 0))) =
    Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 2).obj l.domain 0
      (SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (R.cocomplex.X 2) l.domain
        ((GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 2
          ((ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf).hom.app (op (⊤ : Opens X)) t))) a
  rw [Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict, l.oneResolutionLift_d hS R f hf, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp,
    Cech.GlobalCoordinates.abelianCechGlobalAugmentation_coordinates]
  let e := (CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{0} isTerminalTop).app (R.cocomplex.X 2)
  change Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 2) le_top
    ((ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf).hom.app (op (⊤ : Opens X)) t) =
    Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 2) le_top
      (e.hom (e.inv ((ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf).hom.app (op (⊤ : Opens X)) t)))
  rw [e.inv_hom_id_apply]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
