import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientEuler

/-! # Isomorphism Cohomology Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.IsomorphismCohomologyDimension

noncomputable section

/-! An isomorphism between field spectra induces the actual coefficient-field isomorphism, and its restriction of scalars preserves every individual cohomology dimension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def specIsoRingEquiv {K B : Type u} [CommRing K] [CommRing B]
    (c : Spec (.of B) ⟶ Spec (.of K)) [IsIso c] : K ≃+* B := by
  let e : CommRingCat.of K ≅ .of B := {
    hom := Spec.preimage c
    inv := Spec.preimage (inv c)
    hom_inv_id := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id]
      exact IsIso.inv_hom_id c
    inv_hom_id := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id]
      exact IsIso.hom_inv_id c }
  exact e.commRingCatIsoToRingEquiv

theorem specIsoRingEquiv_specMap {K B : Type u} [CommRing K] [CommRing B]
    (c : Spec (.of B) ⟶ Spec (.of K)) [IsIso c] :
    Spec.map (CommRingCat.ofHom (specIsoRingEquiv c).toRingHom) = c :=
  Spec.map_preimage c

theorem coefficientCohomology_finrank_fieldIso
    {K B : Type u} [Field K] [Field B] {X : Scheme.{u}}
    (e : K ≃+* B) (p : X ⟶ Spec (.of B)) (M : X.Modules) (q : ℕ) :
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (p ≫ Spec.map (CommRingCat.ofHom e.toRingHom))) q).obj M) =
      Module.finrank B ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) := by
  let V := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M
  have h₁ := (CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr
    (HilbertConstruction.Field.CoefficientEuler.schemeCoefficientMap_specMap_comp p e.toRingHom) M q).toLinearEquiv.finrank_eq
  have h₂ := (CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso e.toRingHom (Coefficient.ModulePresheaf.schemeCoefficientMap p) M q).toLinearEquiv.finrank_eq
  exact h₁.trans (h₂.symm.trans (Scalar.EquivalentDimensions.restrictScalars_finrank_of_ringEquiv e V))

theorem coefficientCohomology_finrank_specIso
    {K B : Type u} [Field K] [Field B] {X : Scheme.{u}}
    (c : Spec (.of B) ⟶ Spec (.of K)) [IsIso c]
    (p : X ⟶ Spec (.of B)) (M : X.Modules) (q : ℕ) :
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (p ≫ c)) q).obj M) =
      Module.finrank B ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) := by
  have hmap : Coefficient.ModulePresheaf.schemeCoefficientMap
      (p ≫ Spec.map (CommRingCat.ofHom (specIsoRingEquiv c).toRingHom)) =
      Coefficient.ModulePresheaf.schemeCoefficientMap (p ≫ c) :=
    congrArg (fun k => Coefficient.ModulePresheaf.schemeCoefficientMap (p ≫ k)) (specIsoRingEquiv_specMap c)
  exact ((CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr hmap M q).toLinearEquiv.finrank_eq).symm.trans
    (coefficientCohomology_finrank_fieldIso (specIsoRingEquiv c) p M q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.IsomorphismCohomologyDimension
