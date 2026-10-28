import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneSection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.UnitParameter
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization

/-! # Deformation One Parameter -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneParameter.BundleCycles

noncomputable section

/-! The glued evaluation section has parameter exactly one on every
affine chart, and therefore on the whole original scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

theorem affineDeformationOneSection_parameter {R : Type} [CommRing R] (I : Ideal R) :
    (Spec.map (CommRingCat.ofHom (DeformationProperties.BundleCycles.deformationAtOne I))).appTop
      (Affine.Specialization.BundleCycles.affineDeformationParameterSection I) = 1 := by
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (DeformationProperties.BundleCycles.deformationAtOne I))) (Deformation.Iff.BundleCycles.deformationParameter I)
  change (Scheme.ΓSpecIso (.of R)).inv (DeformationProperties.BundleCycles.deformationAtOne I (Deformation.Iff.BundleCycles.deformationParameter I)) = _ at h
  rw [Deformation.UnitParameter.BundleCycles.deformationAtOne_parameter, map_one] at h
  exact h.symm

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem deformationChartSection_parameter (U : X.AffineZariskiSite) :
    (DeformationProperties.BundleCycles.deformationChartSection I U).appTop (Affine.Specialization.BundleCycles.affineDeformationParameterSection (I.ideal U)) = 1 := by
  change U.2.isoSpec.hom.appTop
    ((Spec.map (CommRingCat.ofHom (DeformationProperties.BundleCycles.deformationAtOne (I.ideal U)))).appTop
      (Affine.Specialization.BundleCycles.affineDeformationParameterSection (I.ideal U))) = 1
  rw [affineDeformationOneSection_parameter, map_one]

theorem globalDeformationOneSection_parameter :
    (DeformationOneSection.BundleCycles.globalDeformationOneSection I).appTop (Specialization.BundleCycles.globalDeformationParameterSection I) = 1 := by
  apply (directedCover X).ext_elem
  intro U
  have hc := congrArg (fun k => k.appTop (Specialization.BundleCycles.globalDeformationParameterSection I))
    (DeformationOneSection.BundleCycles.globalDeformationOneSection_on_chart I U)
  have ht : (DeformationProperties.BundleCycles.deformationChartSection I U).appTop
      (((Deformation.BundleCycles.globalDeformationCover I).f U).appTop (Specialization.BundleCycles.globalDeformationParameterSection I)) = 1 := by
    rw [Specialization.BundleCycles.globalDeformationParameterSection_on_chart]
    exact deformationChartSection_parameter I U
  exact hc.trans (ht.trans (map_one ((directedCover X).f U).appTop.hom).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneParameter.BundleCycles
