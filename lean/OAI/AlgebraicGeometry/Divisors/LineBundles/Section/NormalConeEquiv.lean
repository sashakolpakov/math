import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.PolynomialCoordinates
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.CoordinateCone
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeSymmetric

/-! # Normal Cone Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.NormalConeEquiv.BundleCycles

noncomputable section

/-! # LineBundleCycles: the canonical normal-cone map of a smooth section is an isomorphism -/

open KaehlerDifferential

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] {ι : Type}

theorem sectionNormalCone_coordinate_comparison (v : ι → RingHom.ker (algebraMap B A))
    (b : Module.Basis ι B Ω[B⁄A]) (hb : ∀ i, b i = D A B (v i).val) :
    (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (RingHom.ker (algebraMap B A))).comp
      (Conormal.PolynomialCoordinates.BundleCycles.sectionConormalPolynomialEquiv A B b).toRingHom = CoordinateCone.BundleCycles.sectionCoordinateConeMap v := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap _ (Conormal.PolynomialCoordinates.BundleCycles.sectionConormalPolynomialEquiv A B b (MvPolynomial.C a)) = _
    rw [Conormal.PolynomialCoordinates.BundleCycles.sectionConormalPolynomialEquiv_C, Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap_algebraMap,
      ConormalBasis.BundleCycles.sectionQuotientEquiv_symm_apply, Normal.Cone.BundleCycles.normalConeBaseMap_mk, CoordinateCone.BundleCycles.sectionCoordinateConeMap_C]
  · intro i
    change Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap _ (Conormal.PolynomialCoordinates.BundleCycles.sectionConormalPolynomialEquiv A B b (MvPolynomial.X i)) = _
    rw [Conormal.PolynomialCoordinates.BundleCycles.sectionConormalPolynomialEquiv_X A B v b hb, Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap_generator,
      CoordinateCone.BundleCycles.sectionCoordinateConeMap_X]

theorem sectionNormalConeSymmetricMap_injective_of_coordinates
    (v : ι → RingHom.ker (algebraMap B A)) (b : Module.Basis ι B Ω[B⁄A])
    (hb : ∀ i, b i = D A B (v i).val) :
    Function.Injective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (RingHom.ker (algebraMap B A))) := by
  let := DifferentialCoordinates.BundleCycles.differentialCoordinateAlgebra (R := A) (fun i => (v i).val)
  have : Algebra.FormallyEtale (MvPolynomial ι A) B :=
    DifferentialCoordinates.BundleCycles.differentialCoordinate_formallyEtale (fun i => (v i).val) b hb
  have hi := CoordinateCone.BundleCycles.sectionCoordinateConeMap_injective v (inferInstance : Algebra.FormallySmooth (MvPolynomial ι A) B)
  rw [← sectionNormalCone_coordinate_comparison A B v b hb] at hi
  intro x y h
  obtain ⟨p, rfl⟩ := (Conormal.PolynomialCoordinates.BundleCycles.sectionConormalPolynomialEquiv A B b).surjective x
  obtain ⟨q, rfl⟩ := (Conormal.PolynomialCoordinates.BundleCycles.sectionConormalPolynomialEquiv A B b).surjective y
  exact congrArg (Conormal.PolynomialCoordinates.BundleCycles.sectionConormalPolynomialEquiv A B b) (hi h)

theorem sectionNormalConeSymmetricMap_bijective [Algebra.EssFiniteType A B] [IsLocalRing B] :
    Function.Bijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (RingHom.ker (algebraMap B A))) := by
  obtain ⟨ι, _, v, b, hb⟩ := Smooth.SectionDifferentials.BundleCycles.smoothSection_exists_differentialBasis A B
  exact ⟨sectionNormalConeSymmetricMap_injective_of_coordinates A B v b hb,
    Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap_surjective _⟩

def sectionNormalConeEquiv [Algebra.EssFiniteType A B] [IsLocalRing B] :
    SymmetricAlgebra (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent ≃+*
      Normal.Cone.BundleCycles.NormalConeRing (RingHom.ker (algebraMap B A)) :=
  RingEquiv.ofBijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap _) (sectionNormalConeSymmetricMap_bijective A B)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.NormalConeEquiv.BundleCycles
