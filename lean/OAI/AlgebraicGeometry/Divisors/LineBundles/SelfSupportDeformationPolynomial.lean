import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.CenterPolynomial
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport

/-! # Self Support Deformation Polynomial -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SelfSupportDeformationPolynomial.BundleCycles

noncomputable section

/-! The deformation of the center itself is canonically its constant
polynomial family, compatibly with its actual map to the ambient deformation. -/

variable {R : Type} [CommRing R]

def deformationIdealEqEquiv {I J : Ideal R} (h : I = J) : Deformation.Iff.BundleCycles.deformationAlgebra I ≃ₐ[R] Deformation.Iff.BundleCycles.deformationAlgebra J := by
  subst J
  exact AlgEquiv.refl

theorem deformationIdealEqEquiv_val {I J : Ideal R} (h : I = J) (a : Deformation.Iff.BundleCycles.deformationAlgebra I) :
    (deformationIdealEqEquiv h a).val = a.val := by
  subst J
  rfl

def selfSupportDeformationPolynomialEquiv (I : Ideal R) :
    Polynomial (R ⧸ I) ≃ₐ[R ⧸ I] Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk I)) :=
  (ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv (R ⧸ I)).trans (deformationIdealEqEquiv (Ideal.map_quotient_self I).symm)

theorem selfSupportDeformationPolynomialEquiv_val (I : Ideal R) (a : Polynomial (R ⧸ I)) :
    (selfSupportDeformationPolynomialEquiv I a).val = Polynomial.toLaurent a :=
  deformationIdealEqEquiv_val (Ideal.map_quotient_self I).symm (ZeroIdealDeformation.BundleCycles.zeroDeformationEquiv (R ⧸ I) a)

theorem selfSupportDeformationPolynomialEquiv_symm_val (I : Ideal R)
    (a : Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk I))) :
    Polynomial.toLaurent ((selfSupportDeformationPolynomialEquiv I).symm a) = a.val := by
  rw [← selfSupportDeformationPolynomialEquiv_val, AlgEquiv.apply_symm_apply]

theorem selfSupportDeformationPolynomialEquiv_ambient (I : Ideal R) (a : Deformation.Iff.BundleCycles.deformationAlgebra I) :
    (selfSupportDeformationPolynomialEquiv I).symm (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap I I a) =
      Deformation.CenterPolynomial.BundleCycles.deformationCenterPolynomialMap I (Ideal.Quotient.mk I) (by rw [Ideal.mk_ker]) a := by
  apply Polynomial.toLaurent_injective
  rw [selfSupportDeformationPolynomialEquiv_symm_val, Deformation.CenterPolynomial.BundleCycles.deformationCenterPolynomialMap_toLaurent]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SelfSupportDeformationPolynomial.BundleCycles
