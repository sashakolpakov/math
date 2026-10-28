import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Iteration

/-! # Inverse Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Open.InverseRestriction.Construction

noncomputable section

/-! An actual open inverse identifies the whole specified restriction as an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIso_restrict_of_open_inverse
    {Y X : Scheme.{u}} (π : Y ⟶ X) (U : X.Opens) (j : U.toScheme ⟶ Y) [IsOpenImmersion j]
    (hfac : j ≫ π = U.ι) (hrange : j.opensRange = π ⁻¹ᵁ U) : IsIso (π ∣_ U) := by
  have hr : Set.range j = Set.range (π ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun V : Y.Opens => (V : Set Y)) hrange
  let e := IsOpenImmersion.isoOfRangeEq j (π ⁻¹ᵁ U).ι hr
  have he : e.hom ≫ (π ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac, hfac, Category.id_comp]
  refine ⟨e.hom, ?_, he⟩
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, he, Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Open.InverseRestriction.Construction
