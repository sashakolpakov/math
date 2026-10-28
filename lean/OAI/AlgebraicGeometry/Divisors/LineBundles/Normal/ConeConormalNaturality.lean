import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ConormalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeSymmetric
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps

/-! # Cone Conormal Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeConormalNaturality.BundleCycles

noncomputable section

/-! # LineBundleCycles: the canonical normal-cone map commutes with actual coefficient restrictions -/

variable {R S : Type} [CommRing R] [CommRing S]

theorem normalConeMap_baseMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (a : R ⧸ I) :
    Deformation.Maps.BundleCycles.normalConeMap I J f hf (Cone.BundleCycles.normalConeBaseMap I a) =
      Cone.BundleCycles.normalConeBaseMap J (Ideal.quotientMap J f hf a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Cone.BundleCycles.normalConeBaseMap_mk, Ideal.quotientMap_mk, Cone.BundleCycles.normalConeBaseMap_mk]
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  exact Polynomial.map_C f

theorem normalConeMap_degreeOne (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (a : I) :
    Deformation.Maps.BundleCycles.normalConeMap I J f hf (Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal I) (ConeSymmetric.BundleCycles.reesDegreeOne I a)) =
      Ideal.Quotient.mk (Cone.BundleCycles.normalConeIdeal J) (ConeSymmetric.BundleCycles.reesDegreeOne J ⟨f a.val, hf a.property⟩) := by
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  exact Polynomial.map_monomial f

theorem normalConeSymmetricMap_naturality (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    (ConeSymmetric.BundleCycles.normalConeSymmetricMap J).comp (Conormal.ConormalRestriction.BundleCycles.conormalSymmetricRestriction I J f hf) =
      (Deformation.Maps.BundleCycles.normalConeMap I J f hf).comp (ConeSymmetric.BundleCycles.normalConeSymmetricMap I) := by
  refine Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext (R := R ⧸ I) (M := I.Cotangent) (T := Cone.BundleCycles.NormalConeRing J)
    ((ConeSymmetric.BundleCycles.normalConeSymmetricMap J).comp (Conormal.ConormalRestriction.BundleCycles.conormalSymmetricRestriction I J f hf))
    ((Deformation.Maps.BundleCycles.normalConeMap I J f hf).comp (ConeSymmetric.BundleCycles.normalConeSymmetricMap I)) ?_ ?_
  · intro a
    change ConeSymmetric.BundleCycles.normalConeSymmetricMap J (Conormal.ConormalRestriction.BundleCycles.conormalSymmetricRestriction I J f hf (algebraMap _ _ a)) =
      Deformation.Maps.BundleCycles.normalConeMap I J f hf (ConeSymmetric.BundleCycles.normalConeSymmetricMap I (algebraMap _ _ a))
    rw [Conormal.ConormalRestriction.BundleCycles.conormalSymmetricRestriction_algebraMap, ConeSymmetric.BundleCycles.normalConeSymmetricMap_algebraMap,
      ConeSymmetric.BundleCycles.normalConeSymmetricMap_algebraMap, normalConeMap_baseMap]
  · intro a
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective a
    change ConeSymmetric.BundleCycles.normalConeSymmetricMap J (Conormal.ConormalRestriction.BundleCycles.conormalSymmetricRestriction I J f hf (SymmetricAlgebra.ι _ _ _)) =
      Deformation.Maps.BundleCycles.normalConeMap I J f hf (ConeSymmetric.BundleCycles.normalConeSymmetricMap I (SymmetricAlgebra.ι _ _ _))
    rw [Conormal.ConormalRestriction.BundleCycles.conormalSymmetricRestriction_generator, ConeSymmetric.BundleCycles.normalConeSymmetricMap_generator,
      ConeSymmetric.BundleCycles.normalConeSymmetricMap_generator, normalConeMap_degreeOne]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeConormalNaturality.BundleCycles
