import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ResolutionPullbackEdges

/-! # Cech Resolution Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechResolutionFactorization

noncomputable section

/-! The original Čech-to-sheaf map factors through actual top sections
of the chosen resolution and the already normalized native comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
    (F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) (hU : iSup U = ⊤) (n : ℕ)

def nativeCechTopResolutionHomologyIso :
    (Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex (injectiveResolution F).cocomplex).homology (n + 1) ≅
      ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).total (.up ℕ)).homology (n + 1) := by
  let T : Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex (injectiveResolution F).cocomplex ⟶
      (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).total (.up ℕ) :=
    Comparison.Betti.Cech.TopTotalAugmentation.topCechTotalAugmentation U (injectiveResolution F).cocomplex
  have hT : QuasiIso T :=
    Comparison.Betti.Cech.TopTotalAugmentation.topCechTotalAugmentation_quasiIso U (injectiveResolution F).cocomplex hU (DivisorClass.Chern.Cech.DegreeOneBoundary.injectiveResolution_flasque F)
  letI : IsIso (HomologicalComplex.homologyMap T (n + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap T (n + 1)).mp
      ((quasiIso_iff T).mp hT (n + 1))
  exact asIso (HomologicalComplex.homologyMap T (n + 1))

def nativeCechToTopResolution :
    ((CategoryTheory.cechComplexFunctor U).obj F.obj).homology (n + 1) ⟶
      (Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex (injectiveResolution F).cocomplex).homology (n + 1) :=
  HomologicalComplex.homologyMap
      (DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge U ((injectiveResolution F).ι.f 0) (injectiveResolution F).ι_f_zero_comp_complex_d) (n + 1) ≫
    (nativeCechTopResolutionHomologyIso U F hU n).inv

theorem nativeCechToTopResolution_toSheaf :
    nativeCechToTopResolution U F hU n ≫ SectionComparisonPullback.nativeTopResolutionCohomologyMap F n =
      DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf U F hU n := by
  let R := injectiveResolution F
  let e := DivisorClass.Chern.GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex
  let h := DivisorClass.Chern.FlasqueCechD.abelianFlasqueCechHomologyIso U R.cocomplex (DivisorClass.Chern.Cech.DegreeOneBoundary.injectiveResolution_flasque F) hU n
  let t := nativeCechTopResolutionHomologyIso U F hU n
  let q := HomologicalComplex.homologyMap e.inv (n + 1)
  have he : e.inv ≫ DivisorClass.Chern.FlasqueCechD.abelianCechHorizontalEdge U R.cocomplex = Comparison.Betti.Cech.TopTotalAugmentation.topCechTotalAugmentation U R.cocomplex := rfl
  have ht : q ≫ h.hom = t.hom :=
    (HomologicalComplex.homologyMap_comp e.inv (DivisorClass.Chern.FlasqueCechD.abelianCechHorizontalEdge U R.cocomplex) (n + 1)).symm.trans
      (congrArg (fun g => HomologicalComplex.homologyMap g (n + 1)) he)
  have hi : t.inv ≫ q = h.inv := by
    apply (cancel_mono h.hom).mp
    exact (Category.assoc t.inv q h.hom).trans
      ((congrArg (t.inv ≫ ·) ht).trans (t.inv_hom_id.trans h.inv_hom_id.symm))
  rw [← DivisorClass.Chern.Cech.DegreeOneBoundary.abelianCechToSheaf_native U F hU n]
  change (_ ≫ t.inv) ≫ (q ≫ (DivisorClass.Chern.GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom) =
    (_ ≫ h.inv) ≫ (DivisorClass.Chern.GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom
  let b := HomologicalComplex.homologyMap
    (DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge U (R.ι.f 0) R.ι_f_zero_comp_complex_d) (n + 1)
  let s := (DivisorClass.Chern.GammaSectionsComparison.nativeInjectiveCohomologyIso F n).hom
  exact (Category.assoc b t.inv (q ≫ s)).trans
    ((congrArg (b ≫ ·) ((Category.assoc t.inv q s).symm.trans (congrArg (· ≫ s) hi))).trans
      (Category.assoc b h.inv s).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechResolutionFactorization
