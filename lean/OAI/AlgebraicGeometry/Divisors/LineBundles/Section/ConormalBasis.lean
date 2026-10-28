import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCoordinates
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! # Conormal Basis -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalBasis.BundleCycles

noncomputable section

/-! # LineBundleCycles: the coordinate conormal basis over the actual quotient ring -/

open KaehlerDifferential

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A]

def sectionQuotientEquiv : B ⧸ RingHom.ker (algebraMap B A) ≃+* A :=
  (algebraMap B A).quotientKerEquivOfSurjective (Smooth.SectionCotangent.BundleCycles.algebraSection_surjective A B)

theorem sectionQuotientEquiv_symm_apply (a : A) :
    (sectionQuotientEquiv A B).symm a =
      Ideal.Quotient.mk (RingHom.ker (algebraMap B A)) (algebraMap A B a) := by
  apply (sectionQuotientEquiv A B).injective
  rw [RingEquiv.apply_symm_apply]
  exact (IsScalarTower.algebraMap_apply A B A a)

theorem sectionQuotientEquiv_smul (a : A) (m : (RingHom.ker (algebraMap B A)).Cotangent) :
    (sectionQuotientEquiv A B).symm a • m = a • m := by
  rw [sectionQuotientEquiv_symm_apply]
  change (algebraMap B (B ⧸ RingHom.ker (algebraMap B A)) (algebraMap A B a)) • m = a • m
  rw [algebraMap_smul, algebraMap_smul]

variable [Algebra.FormallySmooth A B] {ι : Type}

def sectionQuotientConormalBasis (b : Module.Basis ι B Ω[B⁄A]) :
    Module.Basis ι (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent :=
  (Smooth.SectionCoordinates.BundleCycles.sectionCoordinateConormalBasis A B b).mapCoeffs (sectionQuotientEquiv A B).symm
    (sectionQuotientEquiv_smul A B)

theorem sectionQuotientConormalBasis_apply (v : ι → RingHom.ker (algebraMap B A))
    (b : Module.Basis ι B Ω[B⁄A]) (hb : ∀ i, b i = D A B (v i).val) (i : ι) :
    sectionQuotientConormalBasis A B b i = Ideal.toCotangent _ (v i) := by
  rw [sectionQuotientConormalBasis, Module.Basis.mapCoeffs_apply,
    Smooth.SectionCoordinates.BundleCycles.sectionCoordinateConormalBasis_apply A B v b hb]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalBasis.BundleCycles
