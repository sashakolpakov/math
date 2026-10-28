import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EulerPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.EquivalentDimensions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.CohomologyRestriction

/-! # Coefficient Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientEuler

noncomputable section

/-! Genuine Euler characteristic is unchanged by an isomorphism of coefficient fields. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem schemeCoefficientMap_specMap_comp
    {R A : Type u} [CommRing R] [CommRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (φ : R →+* A) :
    Coefficient.ModulePresheaf.schemeCoefficientMap (p ≫ Spec.map (CommRingCat.ofHom φ)) = (Coefficient.ModulePresheaf.schemeCoefficientMap p).comp φ := by
  ext r
  change p.appTop ((Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
    p.appTop ((Scheme.ΓSpecIso (.of A)).inv (φ r))
  exact congrArg p.appTop (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) r).symm

theorem coefficientEulerCharacteristic_fieldIso
    {K F : Type u} [Field K] [Field F] {X : Scheme.{u}}
    (e : K ≃+* F) (p : X ⟶ Spec (.of F)) (M : X.Modules) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (p ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) M =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M := by
  apply finsum_congr
  intro q
  let H := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M
  have h₁ := (CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr
    (schemeCoefficientMap_specMap_comp p e.toRingHom) M q).toLinearEquiv.finrank_eq
  have h₂ := (CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso e.toRingHom (Coefficient.ModulePresheaf.schemeCoefficientMap p) M q).toLinearEquiv.finrank_eq
  have h₃ := Scalar.EquivalentDimensions.restrictScalars_finrank_of_ringEquiv e H
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ)) (h₁.trans (h₂.symm.trans h₃))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientEuler
