import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.LocalizationSmooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.SpecialPrime
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSectionDeformationSmooth

/-! # Deformation Special Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.DeformationSpecialSmooth.BundleCycles

noncomputable section

/-! Formal smoothness at every point of the special fiber of a genuine
smooth section, using its localized center and actual deformation algebra. -/

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B]
    [IsNoetherianRing A] [IsNoetherianRing B]

theorem sectionDeformation_isSmoothAt_special
    (q : PrimeSpectrum (Deformation.Iff.BundleCycles.deformationAlgebra (RingHom.ker (algebraMap B A))))
    (hq : Deformation.Iff.BundleCycles.deformationParameter (RingHom.ker (algebraMap B A)) ∈ q.asIdeal) :
    Algebra.IsSmoothAt A q.asIdeal := by
  let I := RingHom.ker (algebraMap B A)
  let b := q.asIdeal.comap (algebraMap B (Deformation.Iff.BundleCycles.deformationAlgebra I))
  have hI : I ≤ b := Deformation.SpecialPrime.BundleCycles.deformationSpecialPrime_liesOver_center I q hq
  let a : Ideal A := b.map (algebraMap B A)
  let : a.IsPrime := Ideal.map_isPrime_of_surjective (Smooth.SectionCotangent.BundleCycles.algebraSection_surjective A B) hI
  have ha : a.comap (algebraMap B A) = b := by
    change (b.map (algebraMap B A)).comap (algebraMap B A) = b
    rw [Ideal.comap_map_of_surjective _ (Smooth.SectionCotangent.BundleCycles.algebraSection_surjective A B)]
    exact sup_of_le_left hI
  apply Deformation.LocalizationSmooth.BundleCycles.deformation_isSmoothAt_of_coefficientLocalization A B I q
  have h := LocalizedSectionDeformationSmooth.BundleCycles.localizedSection_deformation_formallySmooth A B a
  change Algebra.FormallySmooth A (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (algebraMap B (Localization.AtPrime b))))
  exact Deformation.LocalizationSmooth.BundleCycles.deformationLocalization_formallySmooth_congr A B I ha h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.DeformationSpecialSmooth.BundleCycles
