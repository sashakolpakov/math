import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterVanishingIdeal

/-! # Rational Point Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RationalPointIdeal

noncomputable section

/-! A rational section of an affine scheme determines its actual maximal coordinate ideal and a canonical quotient isomorphism with the ground field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {T : Scheme.{u}} [IsAffine T]

theorem affineCoordinateMap_specBaseCoefficientMap
    {B : Type u} [CommRing B] (j : Spec (.of B) ⟶ T) :
    QuotientCoefficientMap.affineCoordinateMap (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j) = j := by
  dsimp only [QuotientCoefficientMap.affineCoordinateMap]
  rw [QuotientCoefficientMap.specBaseCoefficientMap_specMap, Category.assoc, T.isoSpec.hom_inv_id, Category.comp_id]

def affineRationalPointIdeal {K : Type u} [Field K] (z : Spec (.of K) ⟶ T) : Ideal Γ(T, ⊤) :=
  (T.isoSpec.hom (z (IsLocalRing.closedPoint K))).asIdeal

theorem affineRationalPointIdeal_eq_kernel
    {K : Type u} [Field K] (z : Spec (.of K) ⟶ T) :
    affineRationalPointIdeal z = RingHom.ker (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap z) := by
  have h := ParameterVanishingIdeal.affineCoordinateMap_closedPoint_ideal (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap z)
  rwa [affineCoordinateMap_specBaseCoefficientMap] at h

theorem affineRationalPoint_coefficient_surjective
    {K : Type u} [Field K] (p : T ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ T)
    (hz : z ≫ p = 𝟙 _) : Function.Surjective (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap z) := by
  have : IsClosedImmersion z := isClosedImmersion_of_comp_eq_id p z hz
  exact HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap_surjective z

theorem affineRationalPointIdeal_isMaximal
    {K : Type u} [Field K] (p : T ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ T)
    (hz : z ≫ p = 𝟙 _) : (affineRationalPointIdeal z).IsMaximal := by
  rw [affineRationalPointIdeal_eq_kernel]
  exact RingHom.ker_isMaximal_of_surjective _ (affineRationalPoint_coefficient_surjective p z hz)

def affineRationalPointQuotientEquiv
    {K : Type u} [Field K] (p : T ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ T)
    (hz : z ≫ p = 𝟙 _) : (Γ(T, ⊤) ⧸ affineRationalPointIdeal z) ≃+* K := by
  rw [affineRationalPointIdeal_eq_kernel]
  exact (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap z).quotientKerEquivOfSurjective
    (affineRationalPoint_coefficient_surjective p z hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RationalPointIdeal
