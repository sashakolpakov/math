import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneParameter
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneUniqueness
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowLocalization

/-! # Deformation One Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneFiber.BundleCycles

noncomputable section

/-! The global evaluation section lies in the actual punctured family.
Every morphism with parameter one is its composite with the projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem globalDeformation_one_factorization {T : Scheme.{0}} (f : T ⟶ Deformation.BundleCycles.globalDeformation I)
    (hf : f.appTop (Specialization.BundleCycles.globalDeformationParameterSection I) = 1) :
    f = (f ≫ Deformation.BundleCycles.globalDeformationProjection I) ≫ DeformationOneSection.BundleCycles.globalDeformationOneSection I := by
  apply DeformationOneUniqueness.BundleCycles.globalDeformationOne_hom_ext I
  · rw [Category.assoc, DeformationOneSection.BundleCycles.globalDeformationOneSection_projection, Category.comp_id]
  · exact hf
  · change (f ≫ Deformation.BundleCycles.globalDeformationProjection I).appTop
      ((DeformationOneSection.BundleCycles.globalDeformationOneSection I).appTop (Specialization.BundleCycles.globalDeformationParameterSection I)) = 1
    rw [DeformationOneParameter.BundleCycles.globalDeformationOneSection_parameter, map_one]

theorem globalDeformationOneSection_range :
    Set.range (DeformationOneSection.BundleCycles.globalDeformationOneSection I) ⊆ Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) := by
  change Set.range (DeformationOneSection.BundleCycles.globalDeformationOneSection I) ⊆ Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).ι
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have h := Scheme.preimage_basicOpen_top (DeformationOneSection.BundleCycles.globalDeformationOneSection I) (Specialization.BundleCycles.globalDeformationParameterSection I)
  rw [DeformationOneParameter.BundleCycles.globalDeformationOneSection_parameter, Scheme.basicOpen_one] at h
  change x ∈ DeformationOneSection.BundleCycles.globalDeformationOneSection I ⁻¹ᵁ
    (Deformation.BundleCycles.globalDeformation I).basicOpen (Specialization.BundleCycles.globalDeformationParameterSection I)
  rw [h]
  trivial

def globalDeformationOnePunctured : X ⟶ Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I :=
  IsOpenImmersion.lift (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (DeformationOneSection.BundleCycles.globalDeformationOneSection I)
    (globalDeformationOneSection_range I)

theorem globalDeformationOnePunctured_inclusion :
    globalDeformationOnePunctured I ≫ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I =
      DeformationOneSection.BundleCycles.globalDeformationOneSection I := IsOpenImmersion.lift_fac _ _ _

theorem globalDeformationOnePunctured_projection :
    globalDeformationOnePunctured I ≫
      (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ Deformation.BundleCycles.globalDeformationProjection I) = 𝟙 X := by
  rw [← Category.assoc, globalDeformationOnePunctured_inclusion, DeformationOneSection.BundleCycles.globalDeformationOneSection_projection]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationOneFiber.BundleCycles
