import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecPrincipalImageIdeal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization

/-! # Special Fiber Principal Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecialFiberPrincipalKernel.BundleCycles

noncomputable section

/-! The affine special-fiber quotient has the original deformation parameter as its exact global-section kernel generator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineSpecialFiber_principal_kernel {R : Type} [CommRing R] (J : Ideal R) :
    RingHom.ker (Spec.map (R := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra J))
      (S := CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing J))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)))).appTop.hom =
    Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra J))).inv (Deformation.Iff.BundleCycles.deformationParameter J)} := by
  have hk : RingHom.ker (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)) = Deformation.Iff.BundleCycles.deformationSpecialIdeal J := Ideal.mk_ker
  have hk' : RingHom.ker (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)) =
      Ideal.span {Deformation.Iff.BundleCycles.deformationParameter J} := by
    simpa only [Deformation.Iff.BundleCycles.deformationSpecialIdeal] using hk
  exact @SpecPrincipalImageIdeal.BundleCycles.specMap_principal_kernel (Deformation.Iff.BundleCycles.deformationAlgebra J) (SpecialFiber.BundleCycles.DeformationSpecialRing J)
    inferInstance inferInstance (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)) (Deformation.Iff.BundleCycles.deformationParameter J) hk'

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecialFiberPrincipalKernel.BundleCycles
