import OAI.AlgebraicGeometry.DivisorClass.Chern.TransitionCechCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.GlobalCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary

/-! # Transition Intrinsic Resolution -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Original local resolution lifts in the two axes of the native Cech bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) {t : S.X₃.obj.obj (op (⊤ : Opens X))}
  (l : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g t) (R : InjectiveResolution S.X₁)

def Sheaf.CohomologyLifts.SheafLocalLiftCover.nativeResolutionLift : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex l.domain R.cocomplex).X 0).X 0 :=
  (Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 0).obj l.domain 0).symm
    (Cech.LocalSections.abelianCechLocalSections l.domain (R.cocomplex.X 0) (l.resolutionLift hS R))

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.nativeResolutionLift_delta :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex l.domain R.cocomplex).X 0).d 0 1 (l.nativeResolutionLift hS R) =
      ((CategoryTheory.cechComplexFunctor l.domain).map (R.ι.f 0).hom).f 1
        ((Abelian.CechCoordinates.abelianCechCoordinates S.X₁.obj l.domain 1).symm (l.transitionCech hS)) := by
  change ((CategoryTheory.cechComplexFunctor l.domain).obj (R.cocomplex.X 0).obj).d 0 1
    ((Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 0).obj l.domain 0).symm
      (Cech.LocalSections.abelianCechLocalSections l.domain (R.cocomplex.X 0) (l.resolutionLift hS R))) = _
  rw [Cech.IntrinsicOperators.abelianCechCoordinates_symm_d]
  have he := Cech.IntrinsicOperators.abelianCechCoordinates_symm_coefficient (F := S.X₁.obj)
    (G := (R.cocomplex.X 0).obj) l.domain (R.ι.f 0).hom 1 (l.transitionCech hS)
  exact (congrArg (Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 0).obj l.domain 1).symm
    (l.transitionCech_resolution hS R).symm).trans he.symm

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.nativeResolutionLift_d :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex l.domain R.cocomplex).d 0 1).f 0 (l.nativeResolutionLift hS R) =
      FlasqueCechD.abelianCechHorizontalAugmentation l.domain R.cocomplex 1
        ((GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 1
          (Chern.Sheaf.BoundaryResolution.sheafConnectingResolutionSection hS R t)) := by
  apply (Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj l.domain 0).injective
  funext a
  change Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj l.domain 0
      (((CategoryTheory.cechComplexFunctor l.domain).map (R.cocomplex.d 0 1).hom).f 0
        ((Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 0).obj l.domain 0).symm
          (Cech.LocalSections.abelianCechLocalSections l.domain (R.cocomplex.X 0) (l.resolutionLift hS R)))) a = _
  rw [Abelian.CechCoordinates.abelianCechCoordinates_naturality, AddEquiv.apply_symm_apply]
  change (R.cocomplex.d 0 1).hom.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection l.domain a))
    (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le l.domain a 0)
      (l.resolutionLift hS R (a 0))) =
    Abelian.CechCoordinates.abelianCechCoordinates (R.cocomplex.X 1).obj l.domain 0
      (SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (R.cocomplex.X 1) l.domain
        ((GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 1
          (Chern.Sheaf.BoundaryResolution.sheafConnectingResolutionSection hS R t))) a
  rw [Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict, l.resolutionLift_d hS R, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp,
    Cech.GlobalCoordinates.abelianCechGlobalAugmentation_coordinates]
  let e := (CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{0} isTerminalTop).app (R.cocomplex.X 1)
  change Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 1) le_top (Chern.Sheaf.BoundaryResolution.sheafConnectingResolutionSection hS R t) =
    Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (R.cocomplex.X 1) le_top (e.hom (e.inv (Chern.Sheaf.BoundaryResolution.sheafConnectingResolutionSection hS R t)))
  rw [e.inv_hom_id_apply]

end

/-! The actual Cech-to-sheaf class of the original local transitions is the connecting class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) {t : S.X₃.obj.obj (op (⊤ : Opens X))}
  (l : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g t)

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionCech_sheaf_class :
    Abelian.CechClasses.abelianCechSheafClass (X := X) l.domain S.X₁ l.iSup_domain 0
      (l.transitionCech hS) (l.transitionCech_closed hS) =
      ((CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm t).comp hS.extClass (zero_add 1) := by
  let R := injectiveResolution S.X₁
  let s := Chern.Sheaf.BoundaryResolution.sheafConnectingResolutionSection hS R t
  have hs := Chern.Sheaf.BoundaryResolution.sheafConnectingResolutionSection_closed hS R t
  let x := (GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 1 s
  have hx := Intrinsic.ResolutionInjective.nativeResolutionTopSection_closed S.X₁ 0 s hs
  let k := (Abelian.CechCoordinates.abelianCechCoordinates S.X₁.obj l.domain 1).symm (l.transitionCech hS)
  have hk := Abelian.CechClasses.abelianCechNative_closed l.domain S.X₁.obj 1
    (l.transitionCech hS) (l.transitionCech_closed hS)
  have hg := Cech.DegreeOneBoundary.cechDegreeOne_gamma_class l.domain (R.ι.f 0) R.ι_f_zero_comp_complex_d
    k x (l.nativeResolutionLift hS R) (l.nativeResolutionLift_delta hS R)
    (l.nativeResolutionLift_d hS R) hk hx (Cech.DegreeOneBoundary.injectiveResolution_flasque S.X₁) l.iSup_domain
  change FlasqueCechD.abelianCechFlasqueComparison l.domain (Cech.DegreeOneBoundary.injectiveResolution_flasque S.X₁)
    (R.ι.f 0) R.ι_f_zero_comp_complex_d l.iSup_domain 0
    (Abelian.CechClasses.abelianCechNativeClass l.domain S.X₁.obj 0 (l.transitionCech hS)
      (l.transitionCech_closed hS)) =
      -(FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ x hx) at hg
  have hc := ConcreteCategory.congr_hom (Cech.DegreeOneBoundary.abelianCechToSheaf_native l.domain S.X₁ l.iSup_domain 0)
    (Abelian.CechClasses.abelianCechNativeClass l.domain S.X₁.obj 0 (l.transitionCech hS) (l.transitionCech_closed hS))
  change (GammaSectionsComparison.nativeInjectiveCohomologyIso S.X₁ 0).hom
    (FlasqueCechD.abelianCechFlasqueComparison l.domain (Cech.DegreeOneBoundary.injectiveResolution_flasque S.X₁)
      (R.ι.f 0) R.ι_f_zero_comp_complex_d l.iSup_domain 0
      (Abelian.CechClasses.abelianCechNativeClass l.domain S.X₁.obj 0 (l.transitionCech hS)
        (l.transitionCech_closed hS))) =
      Abelian.CechClasses.abelianCechSheafClass l.domain S.X₁ l.iSup_domain 0
        (l.transitionCech hS) (l.transitionCech_closed hS) at hc
  rw [hg, map_neg] at hc
  have hv := Intrinsic.ResolutionInjective.nativeInjectiveCohomologyIso_sectionClass S.X₁ 0 s hs
  change (GammaSectionsComparison.nativeInjectiveCohomologyIso S.X₁ 0).hom
    ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).homologyπ 1 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 0 _ x hx)) =
      Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass R 1 s hs at hv
  exact hc.symm.trans ((congrArg Neg.neg hv).trans (Chern.Sheaf.BoundaryResolution.sheafConnectingBoundary_resolution hS R t).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
