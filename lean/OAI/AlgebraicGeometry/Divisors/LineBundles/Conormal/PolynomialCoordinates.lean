import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalBasis

/-! # Polynomial Coordinates -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.PolynomialCoordinates.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual polynomial coordinates on the conormal symmetric algebra -/

open KaehlerDifferential

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] {ι : Type}

def sectionConormalPolynomialEquiv (b : Module.Basis ι B Ω[B⁄A]) :
    MvPolynomial ι A ≃+*
      SymmetricAlgebra (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent :=
  (MvPolynomial.mapEquiv ι (Section.ConormalBasis.BundleCycles.sectionQuotientEquiv A B).symm).trans
    (SymmetricAlgebra.equivMvPolynomial (Section.ConormalBasis.BundleCycles.sectionQuotientConormalBasis A B b)).symm.toRingEquiv

theorem sectionConormalPolynomialEquiv_C (b : Module.Basis ι B Ω[B⁄A]) (a : A) :
    sectionConormalPolynomialEquiv A B b (MvPolynomial.C a) =
      algebraMap (B ⧸ RingHom.ker (algebraMap B A))
        (SymmetricAlgebra (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent)
        ((Section.ConormalBasis.BundleCycles.sectionQuotientEquiv A B).symm a) := by
  change (SymmetricAlgebra.equivMvPolynomial (Section.ConormalBasis.BundleCycles.sectionQuotientConormalBasis A B b)).symm
    (MvPolynomial.map (Section.ConormalBasis.BundleCycles.sectionQuotientEquiv A B).symm.toRingHom (MvPolynomial.C a)) = _
  rw [MvPolynomial.map_C]
  exact (SymmetricAlgebra.equivMvPolynomial (Section.ConormalBasis.BundleCycles.sectionQuotientConormalBasis A B b)).symm.commutes _

theorem sectionConormalPolynomialEquiv_X (v : ι → RingHom.ker (algebraMap B A))
    (b : Module.Basis ι B Ω[B⁄A]) (hb : ∀ i, b i = D A B (v i).val) (i : ι) :
    sectionConormalPolynomialEquiv A B b (MvPolynomial.X i) =
      SymmetricAlgebra.ι (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent
        (Ideal.toCotangent _ (v i)) := by
  change (SymmetricAlgebra.equivMvPolynomial (Section.ConormalBasis.BundleCycles.sectionQuotientConormalBasis A B b)).symm
    (MvPolynomial.map (Section.ConormalBasis.BundleCycles.sectionQuotientEquiv A B).symm.toRingHom (MvPolynomial.X i)) = _
  rw [MvPolynomial.map_X, SymmetricAlgebra.equivMvPolynomial_symm_X,
    Section.ConormalBasis.BundleCycles.sectionQuotientConormalBasis_apply A B v b hb]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.PolynomialCoordinates.BundleCycles
