import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DeformationOneUniqueness
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization

/-! # Deformation One Uniqueness -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneUniqueness.BundleCycles

noncomputable section

/-! Uniqueness at parameter one descends along the genuine pullback
charts of the global deformation. The source scheme is arbitrary. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem globalDeformationOne_hom_ext {T : Scheme.{0}} (f g : T ⟶ Deformation.BundleCycles.globalDeformation I)
    (hc : f ≫ Deformation.BundleCycles.globalDeformationProjection I = g ≫ Deformation.BundleCycles.globalDeformationProjection I)
    (hf : f.appTop (Specialization.BundleCycles.globalDeformationParameterSection I) = 1)
    (hg : g.appTop (Specialization.BundleCycles.globalDeformationParameterSection I) = 1) : f = g := by
  let C : T.OpenCover := (Deformation.BundleCycles.globalDeformationCover I).pullback₁ f
  apply C.hom_ext
  intro U
  let a : C.X U ⟶ Deformation.ClosedSupport.BundleCycles.affineDeformation (I.ideal U) := (Deformation.BundleCycles.globalDeformationCover I).pullbackHom f U
  let c : Deformation.ClosedSupport.BundleCycles.affineDeformation (I.ideal U) ⟶ Deformation.BundleCycles.globalDeformation I := (Deformation.BundleCycles.globalDeformationCover I).f U
  let b : Deformation.ClosedSupport.BundleCycles.affineDeformation (I.ideal U) ⟶ U.1.toScheme := (Deformation.BundleCycles.deformationGlueData I).natTrans.app U
  have ha : a ≫ c = C.f U ≫ f := (Deformation.BundleCycles.globalDeformationCover I).pullbackHom_map f U
  have hb : b ≫ U.1.ι = c ≫ Deformation.BundleCycles.globalDeformationProjection I :=
    (Deformation.BundleCycles.deformationGlueData I).ι_toBase U |>.symm
  have hsq : (a ≫ b) ≫ U.1.ι = (C.f U ≫ g) ≫ Deformation.BundleCycles.globalDeformationProjection I := by
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, hc, ← Category.assoc]
  let a' : C.X U ⟶ Deformation.ClosedSupport.BundleCycles.affineDeformation (I.ideal U) :=
    (Deformation.BundleCycles.globalDeformation_chart_isPullback I U).lift (a ≫ b) (C.f U ≫ g) hsq
  have ha'b : a' ≫ b = a ≫ b :=
    (Deformation.BundleCycles.globalDeformation_chart_isPullback I U).lift_fst _ _ _
  have ha'c : a' ≫ c = C.f U ≫ g :=
    (Deformation.BundleCycles.globalDeformation_chart_isPullback I U).lift_snd _ _ _
  have hcoeff : a ≫ Affine.DeformationOneUniqueness.BundleCycles.affineDeformationCoefficientProjection (I.ideal U) =
      a' ≫ Affine.DeformationOneUniqueness.BundleCycles.affineDeformationCoefficientProjection (I.ideal U) := by
    have h := congrArg (fun k => k ≫ U.2.isoSpec.hom) ha'b
    change (a' ≫ (Affine.DeformationOneUniqueness.BundleCycles.affineDeformationCoefficientProjection (I.ideal U) ≫ U.2.isoSpec.inv)) ≫ U.2.isoSpec.hom =
      (a ≫ (Affine.DeformationOneUniqueness.BundleCycles.affineDeformationCoefficientProjection (I.ideal U) ≫ U.2.isoSpec.inv)) ≫ U.2.isoSpec.hom at h
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm
  have ht : c.appTop (Specialization.BundleCycles.globalDeformationParameterSection I) = Affine.Specialization.BundleCycles.affineDeformationParameterSection (I.ideal U) :=
    Specialization.BundleCycles.globalDeformationParameterSection_on_chart I U
  have hat : a.appTop (Affine.Specialization.BundleCycles.affineDeformationParameterSection (I.ideal U)) = 1 := by
    have h := congrArg (fun k => k.appTop (Specialization.BundleCycles.globalDeformationParameterSection I)) ha
    change a.appTop (c.appTop (Specialization.BundleCycles.globalDeformationParameterSection I)) =
      (C.f U).appTop (f.appTop (Specialization.BundleCycles.globalDeformationParameterSection I)) at h
    rw [ht, hf, map_one] at h
    exact h
  have ha't : a'.appTop (Affine.Specialization.BundleCycles.affineDeformationParameterSection (I.ideal U)) = 1 := by
    have h := congrArg (fun k => k.appTop (Specialization.BundleCycles.globalDeformationParameterSection I)) ha'c
    change a'.appTop (c.appTop (Specialization.BundleCycles.globalDeformationParameterSection I)) =
      (C.f U).appTop (g.appTop (Specialization.BundleCycles.globalDeformationParameterSection I)) at h
    rw [ht, hg, map_one] at h
    exact h
  exact ha.symm.trans ((congrArg (fun k => k ≫ c)
    (Affine.DeformationOneUniqueness.BundleCycles.affineDeformationOne_hom_ext (I.ideal U) a a' hcoeff hat ha't)).trans ha'c)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneUniqueness.BundleCycles
