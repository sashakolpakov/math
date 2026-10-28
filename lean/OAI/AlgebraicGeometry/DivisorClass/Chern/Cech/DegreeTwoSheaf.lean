import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary

/-! # Degree Two Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeTwoSheaf

noncomputable section

/-! An actual two-step descent computes the native Cech-to-sheaf class in degree two. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X) (hU : ⨆ i, U i = ⊤)
  (F : TopCat.Sheaf AddCommGrpCat.{0} X)

theorem cechDegreeTwo_sheaf_class
    (k : ((CategoryTheory.cechComplexFunctor U).obj F.obj).X 2)
    (hk : ((CategoryTheory.cechComplexFunctor U).obj F.obj).d 2 3 k = 0)
    (s : ((injectiveResolution F).cocomplex.X 2).obj.obj (op (⊤ : Opens X)))
    (hs : ((injectiveResolution F).cocomplex.d 2 3).hom.app (op (⊤ : Opens X)) s = 0)
    (b : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).X 0).X 1)
    (v : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).X 1).X 0)
    (hb : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).X 0).d 1 2 b =
      ((CategoryTheory.cechComplexFunctor U).map ((injectiveResolution F).ι.f 0).hom).f 2 k)
    (hd : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).d 0 1).f 1 b =
      ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).X 1).d 0 1 v)
    (hv : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).d 1 2).f 0 v =
      FlasqueCechD.abelianCechHorizontalAugmentation U (injectiveResolution F).cocomplex 2
        ((GammaSectionsComparison.abelianGammaSectionsIso (injectiveResolution F).cocomplex).inv.f 2 s)) :
    Abelian.CechComparison.abelianCechToSheaf U F hU 1
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ k hk)) =
      -Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (injectiveResolution F) 2 s hs := by
  let R := injectiveResolution F
  let x := (GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 2 s
  have hx := Intrinsic.ResolutionInjective.nativeResolutionTopSection_closed F 1 s hs
  have hg := DegreeOneBoundary.cechDegreeTwo_gamma_class (F := F) U (R.ι.f 0) R.ι_f_zero_comp_complex_d
    k x b v hb hd hv hk hx (DegreeOneBoundary.injectiveResolution_flasque F) hU
  have hc := ConcreteCategory.congr_hom (DegreeOneBoundary.abelianCechToSheaf_native U F hU 1)
    (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ k hk))
  change (GammaSectionsComparison.nativeInjectiveCohomologyIso F 1).hom
    (FlasqueCechD.abelianCechFlasqueComparison U (DegreeOneBoundary.injectiveResolution_flasque F)
      (R.ι.f 0) R.ι_f_zero_comp_complex_d hU 1
      (((CategoryTheory.cechComplexFunctor U).obj F.obj).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ k hk))) = _ at hc
  have hgs := congrArg (GammaSectionsComparison.nativeInjectiveCohomologyIso F 1).hom hg
  have hn := map_neg (GammaSectionsComparison.nativeInjectiveCohomologyIso F 1).hom.hom
    ((FlasqueCechD.abelianDerivedSectionsComplex R.cocomplex).homologyπ 2 (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ x hx))
  exact hc.symm.trans (hgs.trans (hn.trans
    (congrArg Neg.neg (Intrinsic.ResolutionInjective.nativeInjectiveCohomologyIso_sectionClass F 1 s hs))))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeTwoSheaf
