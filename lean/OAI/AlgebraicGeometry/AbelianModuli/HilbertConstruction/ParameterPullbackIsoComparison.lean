import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualBasePullbackProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Parameter Pullback Iso Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackIsoComparison

noncomputable section

/-! The categorical composition comparison and the geometric Cartesian comparison for parameter pullbacks are the same isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T M : Over S} (c : T ⟶ M) (A : Over S)

theorem overBaseMapPullbackIso_hom_original :
    (HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso c A).hom.left ≫
      pullback.fst (pullback.snd A.hom M.hom) c.left ≫ pullback.fst A.hom M.hom =
      pullback.fst A.hom T.hom := by
  change ((eqToIso (congrArg (fun b => (Over.pullback b).obj A) c.w.symm)).hom.left ≫
    ((Over.pullbackComp c.left M.hom).hom.app A).left) ≫ _ = _
  rw [Category.assoc, Pullback.Comparisons.pullbackComp_hom_fst_fst]
  exact EqualBasePullbackProjections.equalBasePullback_hom_fst A T.hom (c.left ≫ M.hom) c.w.symm

theorem overBaseMapPullbackIso_hom_fst :
    (HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso c A).hom.left ≫ pullback.fst (pullback.snd A.hom M.hom) c.left =
      Single.ParameterBaseChange.singleParameterBaseChangeMap c A := by
  apply (IsPullback.of_hasPullback A.hom M.hom).hom_ext
  · exact (Category.assoc _ _ _).trans
      ((overBaseMapPullbackIso_hom_original c A).trans (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c A).symm)
  · change ((HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso c A).hom.left ≫ pullback.fst (pullback.snd A.hom M.hom) c.left) ≫
      pullback.snd A.hom M.hom = Single.ParameterBaseChange.singleParameterBaseChangeMap c A ≫ pullback.snd A.hom M.hom
    have hw : (HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso c A).hom.left ≫ pullback.snd (pullback.snd A.hom M.hom) c.left =
        pullback.snd A.hom T.hom := (HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso c A).hom.w
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    exact (Single.ParameterFunctoriality.singleParameterBaseChangeMap_over c A).symm

theorem overBaseMapPullbackIso_eq_singleParameter : HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso c A = Single.ParameterBaseChange.singleParameterBaseChangeIso c A := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (overBaseMapPullbackIso_hom_fst c A).trans (Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst c A).symm
  · exact (HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso c A).hom.w.trans (Single.ParameterBaseChange.singleParameterBaseChangeIso c A).hom.w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackIsoComparison
