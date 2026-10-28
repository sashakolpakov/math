import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage

/-! # Prime Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeSupport.BundleCycles

noncomputable section

/-!
# LineBundleCycles: an actual prime quotient represents the geometric prime support

The spectrum of R/P maps by the actual quotient ring homomorphism.
Its integral reduced image has generic point P. The constructed image
isomorphism transports its complete principal divisor to that geometric
support without changing any coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (R : Type) [CommRing R] (P : Ideal R) [P.IsPrime]

abbrev affinePrimePoint : Spec (CommRingCat.of R) := ⟨P, inferInstance⟩

def affinePrimeQuotientMap : Spec (CommRingCat.of (R ⧸ P)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))

instance affinePrimeQuotientMap_isClosedImmersion : IsClosedImmersion (affinePrimeQuotientMap R P) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk P)) Ideal.Quotient.mk_surjective

theorem affinePrimeQuotientMap_genericPoint :
    affinePrimeQuotientMap R P (genericPoint (Spec (CommRingCat.of (R ⧸ P)))) =
      affinePrimePoint R P := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact Ideal.mk_ker

theorem affinePrime_imageClosure :
    CycleClass.Geometric.StratumClosure.integralImageClosure (affinePrimeQuotientMap R P) =
      irreducibleSetEquivPoints.symm (affinePrimePoint R P) := by
  apply irreducibleSetEquivPoints.injective
  rw [irreducibleSetEquivPoints.apply_symm_apply]
  exact (Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint (affinePrimeQuotientMap R P)).trans
    (affinePrimeQuotientMap_genericPoint R P)

def affinePrimeSupportIso :
    Spec (CommRingCat.of (R ⧸ P)) ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure (affinePrimeQuotientMap R P)) :=
  Integral.ClosedImage.BundleCycles.integralClosedImageIso (affinePrimeQuotientMap R P)

theorem affinePrimeSupport_principalDivisor [IsNoetherianRing R]
    (g : (Spec (CommRingCat.of (R ⧸ P))).functionField) :
    Finsupp.mapDomain (affinePrimeQuotientMap R P)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of (R ⧸ P))) g) =
        Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (CycleClass.Geometric.StratumClosure.integralImageClosure (affinePrimeQuotientMap R P))
          (Integral.ClosedImage.BundleCycles.integralClosedImageFunction (affinePrimeQuotientMap R P) g) :=
  Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor (affinePrimeQuotientMap R P) g

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeSupport.BundleCycles
