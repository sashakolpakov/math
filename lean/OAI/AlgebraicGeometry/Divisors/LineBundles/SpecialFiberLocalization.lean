import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization
import OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization

/-! # Special Fiber Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiberLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: localization of the special fiber

The parameter ideal maps to the parameter ideal under every coefficient
homomorphism. Combining the proved deformation localization with quotient
localization shows that the special-fiber rings also commute with base
localization. This is the remaining affine input for gluing the cone fibers.
-/

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The defining equation of the special fiber is preserved, including its ideal. -/
theorem deformationSpecialIdeal_map (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    (Deformation.Iff.BundleCycles.deformationSpecialIdeal I).map (Deformation.Maps.BundleCycles.deformationMap I J f hf) = Deformation.Iff.BundleCycles.deformationSpecialIdeal J := by
  unfold Deformation.Iff.BundleCycles.deformationSpecialIdeal
  rw [Ideal.map_span, Set.image_singleton, Deformation.Maps.BundleCycles.deformationMap_parameter]

variable (I : Ideal R) (M : Submonoid R) (S)
variable [Algebra R S] [IsLocalization M S]

/-- The special fiber over a localized base is the localization of the original
special fiber by the same base denominators. -/
theorem deformationSpecialMap_isLocalization (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hIJ : I ≤ J.comap (algebraMap R S)) :
    letI : Algebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J) :=
      @RingHom.toAlgebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J)
        (by infer_instance) (by infer_instance) (Deformation.Maps.BundleCycles.deformationSpecialMap I J (algebraMap R S) hIJ)
    @IsLocalization (SpecialFiber.BundleCycles.DeformationSpecialRing I) (by infer_instance)
      (@Submonoid.map (Deformation.Iff.BundleCycles.deformationAlgebra I) (SpecialFiber.BundleCycles.DeformationSpecialRing I)
        (by infer_instance) (by infer_instance) (Deformation.Iff.BundleCycles.deformationAlgebra I →* SpecialFiber.BundleCycles.DeformationSpecialRing I)
        (by infer_instance) (by infer_instance) (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I)).toMonoidHom
        (Deformation.Localization.BundleCycles.deformationDenominators I M))
      (SpecialFiber.BundleCycles.DeformationSpecialRing J) (by infer_instance) (by infer_instance) := by
  let : Algebra (Deformation.Iff.BundleCycles.deformationAlgebra I) (Deformation.Iff.BundleCycles.deformationAlgebra J) :=
    (Deformation.Maps.BundleCycles.deformationMap I J (algebraMap R S) hIJ).toAlgebra
  have : IsLocalization (Deformation.Localization.BundleCycles.deformationDenominators I M) (Deformation.Iff.BundleCycles.deformationAlgebra J) :=
    Deformation.Localization.BundleCycles.deformationMap_isLocalization I M S J hJ hIJ
  exact QuotientLocalization.BundleCycles.quotientMap_isLocalization (Deformation.Localization.BundleCycles.deformationDenominators I M) (Deformation.Iff.BundleCycles.deformationAlgebra J)
    (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)
    (deformationSpecialIdeal_map I J (algebraMap R S) hIJ)
    (Deformation.Maps.BundleCycles.deformationMap_specialIdeal I J (algebraMap R S) hIJ)

/-- Constants in the closed fiber provide its map from the original affine base. -/
def specialFiberBaseMap (I : Ideal R) : R →+* SpecialFiber.BundleCycles.DeformationSpecialRing I :=
  (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I)).comp (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I))

/-- Special-fiber restriction to a principal affine open is localization
at the image of the same regular function. -/
theorem deformationSpecialMap_isLocalization_away (r : R)
    [IsLocalization.Away r S] (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hIJ : I ≤ J.comap (algebraMap R S)) :
    letI : Algebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J) :=
      @RingHom.toAlgebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J)
        (by infer_instance) (by infer_instance) (Deformation.Maps.BundleCycles.deformationSpecialMap I J (algebraMap R S) hIJ)
    IsLocalization.Away (specialFiberBaseMap I r) (SpecialFiber.BundleCycles.DeformationSpecialRing J) := by
  let : Algebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J) :=
    @RingHom.toAlgebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J)
      (by infer_instance) (by infer_instance) (Deformation.Maps.BundleCycles.deformationSpecialMap I J (algebraMap R S) hIJ)
  have h := deformationSpecialMap_isLocalization (I := I) (M := Submonoid.powers r) (S := S) J hJ hIJ
  change IsLocalization.Away
    (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I) r))
      (SpecialFiber.BundleCycles.DeformationSpecialRing J)
  simp only [Deformation.Localization.BundleCycles.deformationDenominators, Submonoid.map_powers] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiberLocalization.BundleCycles
