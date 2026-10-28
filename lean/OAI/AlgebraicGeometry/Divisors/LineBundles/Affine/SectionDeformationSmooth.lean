import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.DeformationSpecialSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.PuncturedSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType

/-! # Section Deformation Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionDeformationSmooth.BundleCycles

noncomputable section

/-! The actual deformation algebra of an affine smooth section is smooth
over its base. The special and punctured cases exhaust its prime spectrum. -/

theorem affineSection_deformation_smooth (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra B A] [IsScalarTower A B A] [Algebra.Smooth A B]
    [IsNoetherianRing A] [IsNoetherianRing B] :
    Algebra.Smooth A (Deformation.Iff.BundleCycles.deformationAlgebra (RingHom.ker (algebraMap B A))) := by
  let I := RingHom.ker (algebraMap B A)
  let : Algebra.FiniteType B (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
    Deformation.FiniteType.BundleCycles.deformationAlgebra_finiteType I (IsNoetherian.noetherian I)
  let : Algebra.FiniteType A (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  let : Algebra.FinitePresentation A (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp ?_, inferInstance⟩
  apply Set.eq_univ_iff_forall.mpr
  intro q
  by_cases hq : Deformation.Iff.BundleCycles.deformationParameter I ∈ q.asIdeal
  · exact Section.DeformationSpecialSmooth.BundleCycles.sectionDeformation_isSmoothAt_special A B q hq
  · exact Deformation.PuncturedSmooth.BundleCycles.deformation_isSmoothAt_punctured A B I q hq

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionDeformationSmooth.BundleCycles
