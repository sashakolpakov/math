import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechResolutionFactorization

/-! # Top Resolution Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TopResolutionPullback

noncomputable section

/-! The actual Čech-to-resolution comparison commutes with the
constructed pullback on both native complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {I : Type} (U : I → Opens Y)
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤) (n : ℕ)

theorem nativeCechToTopResolution_pullback :
    HomologicalComplex.homologyMap (Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a.hom) (n + 1) ≫
        Intrinsic.CechResolutionFactorization.nativeCechToTopResolution (fun i => (Opens.map f).obj (U i)) G hV n =
      Intrinsic.CechResolutionFactorization.nativeCechToTopResolution U F hU n ≫
        HomologicalComplex.homologyMap
          (Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a (injectiveResolution F) (injectiveResolution G)) (n + 1) := by
  let R := injectiveResolution F
  let S := injectiveResolution G
  let V := fun i => (Opens.map f).obj (U i)
  let u := Intrinsic.CechResolutionFactorization.nativeCechTopResolutionHomologyIso U F hU n
  let v := Intrinsic.CechResolutionFactorization.nativeCechTopResolutionHomologyIso V G hV n
  let p := HomologicalComplex.homologyMap (Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a.hom) (n + 1)
  let t := HomologicalComplex.homologyMap (ResolutionPullbackEdges.nativeCechResolutionTotalPullback f U a) (n + 1)
  let r := HomologicalComplex.homologyMap (Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a R S) (n + 1)
  let b := HomologicalComplex.homologyMap (DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge U (R.ι.f 0) R.ι_f_zero_comp_complex_d) (n + 1)
  let c := HomologicalComplex.homologyMap (DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge V (S.ι.f 0) S.ι_f_zero_comp_complex_d) (n + 1)
  have hb : b ≫ t = p ≫ c := by
    exact (HomologicalComplex.homologyMap_comp _ _ (n + 1)).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g (n + 1))
        (ResolutionPullbackEdges.nativeCechResolutionPullback_vertical f U a)).trans (HomologicalComplex.homologyMap_comp _ _ (n + 1)))
  have hh : u.hom ≫ t = r ≫ v.hom := by
    exact (HomologicalComplex.homologyMap_comp _ _ (n + 1)).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g (n + 1))
        (ResolutionPullbackEdges.nativeCechResolutionPullback_horizontal f U a hU hV)).trans
          (HomologicalComplex.homologyMap_comp _ _ (n + 1)))
  have hi : t ≫ v.inv = u.inv ≫ r := by
    apply (cancel_epi u.hom).mp
    exact (Category.assoc u.hom t v.inv).symm.trans
      ((congrArg (· ≫ v.inv) hh).trans
        ((Category.assoc r v.hom v.inv).trans
          ((congrArg (r ≫ ·) v.hom_inv_id).trans
            ((Category.comp_id r).trans (u.hom_inv_id_assoc r).symm))))
  change p ≫ (c ≫ v.inv) = (b ≫ u.inv) ≫ r
  exact (Category.assoc p c v.inv).symm.trans
    ((congrArg (· ≫ v.inv) hb.symm).trans
      ((Category.assoc b t v.inv).trans ((congrArg (b ≫ ·) hi).trans (Category.assoc b u.inv r).symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TopResolutionPullback
