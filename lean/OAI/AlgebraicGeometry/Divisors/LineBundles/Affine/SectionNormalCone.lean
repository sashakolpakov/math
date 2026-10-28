import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSectionNormalCone
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeLocalDetection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeSymmetric

/-! # Section Normal Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionNormalCone.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual normal cone of any essentially finite-type smooth ring section -/

theorem normalConeSymmetricMap_top_injective (R : Type) [CommRing R] :
    Function.Injective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (⊤ : Ideal R)) := by
  have : Subsingleton (R ⧸ (⊤ : Ideal R)) := inferInstance
  have : Subsingleton (SymmetricAlgebra (R ⧸ (⊤ : Ideal R)) (⊤ : Ideal R).Cotangent) :=
    Algebra.subsingleton (R ⧸ (⊤ : Ideal R)) _
  exact Function.injective_of_subsingleton _

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B]

theorem affineSection_normalConeSymmetricMap_bijective :
    Function.Bijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (RingHom.ker (algebraMap B A))) := by
  refine ⟨Normal.ConeLocalDetection.BundleCycles.normalConeSymmetricMap_injective_of_localizations _ ?_, Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap_surjective _⟩
  intro p hp
  by_cases hI : RingHom.ker (algebraMap B A) ≤ p
  · let q : Ideal A := p.map (algebraMap B A)
    have : q.IsPrime := Ideal.map_isPrime_of_surjective (Smooth.SectionCotangent.BundleCycles.algebraSection_surjective A B) hI
    have hq : q.comap (algebraMap B A) = p := by
      change (p.map (algebraMap B A)).comap (algebraMap B A) = p
      rw [Ideal.comap_map_of_surjective _ (Smooth.SectionCotangent.BundleCycles.algebraSection_surjective A B)]
      exact sup_of_le_left hI
    have h := (LocalizedSectionNormalCone.BundleCycles.localizedSection_normalConeSymmetricMap_bijective A B q).injective
    exact Normal.ConeLocalDetection.BundleCycles.normalConeSymmetricMap_localization_congr _ hq h
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := Localization.AtPrime p) hI]
    exact normalConeSymmetricMap_top_injective _

def affineSectionNormalConeEquiv :
    SymmetricAlgebra (B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent ≃+*
      Normal.Cone.BundleCycles.NormalConeRing (RingHom.ker (algebraMap B A)) :=
  RingEquiv.ofBijective (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap _) (affineSection_normalConeSymmetricMap_bijective A B)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionNormalCone.BundleCycles
