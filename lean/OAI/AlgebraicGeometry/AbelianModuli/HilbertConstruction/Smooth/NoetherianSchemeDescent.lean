import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredGluedModelExistence

/-! # Noetherian Scheme Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.NoetherianSchemeDescent

noncomputable section

/-! Smooth separated quasi-compact schemes descend to smooth noetherian schemes over finite integral coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_smooth_noetherian_scheme_model_above
    {R : Type u} [CommRing R] (X : Over (Spec (.of R)))
    [CompactSpace X.left] [IsSeparated X.hom] [Smooth X.hom]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ D : Subalgebra ℤ R, C ≤ D ∧ Algebra.FiniteType ℤ D ∧ IsNoetherianRing D ∧
      ∃ Y : Over (Spec (.of D)), Smooth Y.hom ∧ IsNoetherian Y.left ∧
        ∃ q : X.left ⟶ Y.left, IsPullback q X.hom Y.hom
          (Spec.map (CommRingCat.ofHom D.val.toRingHom)) := by
  obtain ⟨M, hCM⟩ := FiniteIntersection.IntersectionModel.exists_finiteIntersectionModel X C
  obtain ⟨D, _, hD, Y, hs, hn, q, hq⟩ := M.exists_recovered_glued_model ⊥ Subalgebra.fg_bot
  have : Algebra.FiniteType M.coefficients D := (Subalgebra.fg_iff_finiteType D).mp hD
  have hft : Algebra.FiniteType ℤ D := Algebra.FiniteType.trans (S := M.coefficients)
    (inferInstanceAs (Algebra.FiniteType ℤ M.coefficients))
    (inferInstanceAs (Algebra.FiniteType M.coefficients D))
  have hnoeth : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing ℤ D
  have hMD : M.coefficients ≤ D.restrictScalars ℤ := by
    intro r hr
    exact D.algebraMap_mem (⟨r, hr⟩ : M.coefficients)
  exact ⟨D.restrictScalars ℤ, hCM.trans hMD, hft, hnoeth, Y, hs, hn, q, hq⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.NoetherianSchemeDescent
